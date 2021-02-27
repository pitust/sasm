#![feature(box_syntax)]
#![feature(unboxed_closures)]
#![feature(io_read_to_string)]
#![feature(option_expect_none)]
use clap::{App, Arg};
use log::{error, trace};
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{borrow::Borrow, collections::HashMap, hash::Hash, io::Write};
use std::{process::exit, usize};

pub mod elf;

#[derive(Parser)]
#[grammar = "grammar.pest"] // relative to src
struct AsmParser;

enum Resolvable {
    Bytes(Vec<u8>),
    Unresolved(
        Box<dyn Fn<(&'static HashMap<String, usize>,), Output = Vec<u8>>>,
        usize,
        HashMap<String, usize>,
    ),
}
fn into_unresolved(
    r: Resolvable,
) -> (
    Box<dyn Fn<(&'static HashMap<String, usize>,), Output = Vec<u8>>>,
    usize,
    HashMap<String, usize>,
) {
    match r {
        Resolvable::Bytes(p) => {
            let l = p.len();
            let p = p.clone();
            return (box move |_a| p.clone(), l, HashMap::new());
        }
        Resolvable::Unresolved(a, b, c) => (a, b, c),
    }
}
fn concat(r: Resolvable, l: Resolvable) -> Resolvable {
    let sizer = match &r {
        Resolvable::Bytes(b) => b.len(),
        Resolvable::Unresolved(_, sz, _) => *sz,
    };
    let sizel = match &l {
        Resolvable::Bytes(b) => b.len(),
        Resolvable::Unresolved(_, sz, _) => *sz,
    };
    let r = into_unresolved(r);
    let l = into_unresolved(l);
    let mut hmprovides = HashMap::new();
    for k in r.2.iter() {
        hmprovides
            .insert(k.0.clone(), *k.1)
            .expect_none("Symbols clashed");
    }
    for k in l.2.iter() {
        hmprovides
            .insert(k.0.clone(), *k.1 + sizer)
            .expect_none("Symbols clashed");
    }
    return Resolvable::Unresolved(
        box move |a| {
            let mut r = r.0(a);
            let l = l.0(a);
            for k in l {
                r.push(k);
            }
            return r;
        },
        sizel + sizer,
        hmprovides,
    );
}

#[derive(Debug, Clone)]
pub enum Expr {
    Label(String),
    Number(isize),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Shl(Box<Expr>, Box<Expr>),
    Shr(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
#[allow(non_camel_case_types)]
pub enum Reg {
    gra,
    grb,
    grc,
    grd,
    gre,
    grf,
    orl,
    orr,
    nrl,
    nrr,
    ara,
    ars,
    arm,
    ard,
    aro,
    bra,
    bro,
    brx,
    brn,
    srr,
    srl,
    nro,
    prs,
    prb,
    mrf,
    mri,
    mre,
    mrn,
    mrp,
}

impl Reg {
    pub fn to_reg(s: &str) -> Option<Reg> {
        match s {
            "gra" => Some(Self::gra),
            "grb" => Some(Self::grb),
            "grc" => Some(Self::grc),
            "grd" => Some(Self::grd),
            "gre" => Some(Self::gre),
            "grf" => Some(Self::grf),
            "orl" => Some(Self::orl),
            "orr" => Some(Self::orr),
            "nrl" => Some(Self::nrl),
            "nrr" => Some(Self::nrr),
            "ara" => Some(Self::ara),
            "ars" => Some(Self::ars),
            "arm" => Some(Self::arm),
            "ard" => Some(Self::ard),
            "aro" => Some(Self::aro),
            "bra" => Some(Self::bra),
            "bro" => Some(Self::bro),
            "brx" => Some(Self::brx),
            "brn" => Some(Self::brn),
            "srr" => Some(Self::srr),
            "srl" => Some(Self::srl),
            "nro" => Some(Self::nro),
            "prs" => Some(Self::prs),
            "prb" => Some(Self::prb),
            "mrf" => Some(Self::mrf),
            "mri" => Some(Self::mri),
            "mre" => Some(Self::mre),
            "mrn" => Some(Self::mrn),
            "mrp" => Some(Self::mrp),
            _ => None,
        }
    }
    pub fn to_id(&self) -> u8 {
        match self {
            Self::gra => 0x04,
            Self::grb => 0x05,
            Self::grc => 0x06,
            Self::grd => 0x07,
            Self::gre => 0x08,
            Self::grf => 0x09,
            Self::orl => 0x0a,
            Self::orr => 0x0b,
            Self::nrl => 0x0c,
            Self::nrr => 0x0d,
            Self::ara => 0x0e,
            Self::ars => 0x0f,
            Self::arm => 0x10,
            Self::ard => 0x11,
            Self::aro => 0x12,
            Self::bra => 0x13,
            Self::bro => 0x14,
            Self::brx => 0x15,
            Self::brn => 0x16,
            Self::srr => 0x17,
            Self::srl => 0x18,
            Self::nro => 0x19,
            Self::prs => 0x1a,
            Self::prb => 0x1b,
            Self::mrf => 0x1c,
            Self::mri => 0x1d,
            Self::mre => 0x1e,
            Self::mrn => 0x1f,
            Self::mrp => 0x20,
        }
    }
    pub fn is_reg(s: String) -> bool {
        Self::to_reg(&s).is_some()
    }
}

#[derive(Debug, Clone)]
enum AsmTerm {
    Reg(Reg),
    Expr(Expr),
    LoadD(Expr),
    // LoadW(Expr),
    // LoadB(Expr),
    LoadDRegoff(Expr, Reg),
    // LoadWRegoff(Expr, Reg),
    // LoadBRegoff(Expr, Reg),
    LoadDReg(Reg),
    // LoadWReg(Reg),
    // LoadBReg(Reg),
    AddReg(Expr, Reg),
    Never,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
enum ExprUsageLimits {
    Int,
    InsnLHS,
    InsnRHS,
}

impl ExprUsageLimits {
    fn covers_lhs(&self) -> bool {
        *self == Self::InsnLHS || *self == Self::InsnRHS
    }
    fn covers_rhs(&self) -> bool {
        *self == Self::InsnRHS
    }
    fn covers_int(&self) -> bool {
        *self == Self::Int || *self == Self::InsnRHS
    }
}

fn parse_number(s: &str) -> isize {
    if s.starts_with("-") {
        return -parse_number(s.split_at(1).1);
    }
    if s.starts_with("0x") {
        isize::from_str_radix(s.split_at(2).1, 16).unwrap()
    } else {
        s.parse().unwrap()
    }
}

fn handle_expr(rule: Pair<'_, Rule>, limits: ExprUsageLimits) -> AsmTerm {
    let str_of_rule = rule.as_str();
    if rule.as_rule() == Rule::asmexpr {
        return handle_expr(rule.into_inner().next().unwrap(), limits);
    }
    if rule.as_rule() == Rule::term {
        return handle_expr(rule.into_inner().next().unwrap(), limits);
    }
    if rule.as_rule() == Rule::num {
        if !limits.covers_int() {
            error!("Invalid RHS-only operand {}!", str_of_rule);
            return AsmTerm::Never;
        }
        return AsmTerm::Expr(Expr::Number(parse_number(str_of_rule)));
    }
    if rule.as_rule() == Rule::aexpr_bracks {
        let mut rule_iter = rule.into_inner();
        rule_iter.next().unwrap();
        rule_iter.next().unwrap();
        return handle_expr(rule_iter.next().unwrap(), limits);
    }
    if rule.as_rule() == Rule::ident {
        if Reg::is_reg(str_of_rule.to_string()) {
            if !limits.covers_lhs() {
                error!("Unable to use a register {}!", str_of_rule);
                return AsmTerm::Never;
            }
            return AsmTerm::Reg(Reg::to_reg(str_of_rule).unwrap());
        }
        if !limits.covers_rhs() {
            error!("Invalid RHS-only operand {}!", str_of_rule);
            return AsmTerm::Never;
        }
        return AsmTerm::Expr(Expr::Label(str_of_rule.to_string()));
    }
    if rule.as_rule() == Rule::aexpr_deref {
        let mut rule_inner = rule.into_inner();
        let kind = rule_inner.next().unwrap().as_str();
        rule_inner.next().unwrap();
        return match handle_expr(rule_inner.next().unwrap(), ExprUsageLimits::InsnRHS) {
            AsmTerm::Expr(expr) => AsmTerm::LoadD(expr),
            AsmTerm::AddReg(expr, reg) => match kind {
                "d" => AsmTerm::LoadDRegoff(expr, reg),
                unk => todo!("{}", unk),
            },
            AsmTerm::Reg(reg) => match kind {
                "d" => AsmTerm::LoadDReg(reg),
                unk => todo!("{}", unk),
            },
            AsmTerm::Never => {
                error!("It's a never! (from {})", str_of_rule);
                AsmTerm::Never
            }
            _ => {
                error!("Invalid nested load {}!", str_of_rule);
                AsmTerm::Never
            }
        };
    }
    if rule.as_rule() == Rule::aexpr_deref_synm {
        return match handle_expr(rule.into_inner().next().unwrap(), ExprUsageLimits::InsnRHS) {
            AsmTerm::Expr(expr) => AsmTerm::LoadD(expr),
            AsmTerm::AddReg(expr, reg) => AsmTerm::LoadDRegoff(expr, reg),
            AsmTerm::Reg(reg) => AsmTerm::LoadDReg(reg),
            AsmTerm::Never => {
                error!("It's a never! (from {})", str_of_rule);
                AsmTerm::Never
            }
            _ => {
                error!("Invalid nested load {}!", str_of_rule);
                AsmTerm::Never
            }
        };
    }

    if rule.as_rule() == Rule::expr {
        let rule_children_vec = rule.into_inner().collect::<Vec<_>>();
        if rule_children_vec.len() == 1 {
            return handle_expr(rule_children_vec.into_iter().next().unwrap(), limits);
        }
        let mut rule_children = rule_children_vec.into_iter().peekable();
        let first_child = handle_expr(rule_children.next().unwrap(), limits);
        #[allow(unused_assignments)]
        let mut expr: Option<Expr> = None;
        match first_child {
            AsmTerm::Expr(e) => {
                expr = Some(e);
            }
            AsmTerm::Never => {
                error!("Propagating never across {}!", str_of_rule);
                return AsmTerm::Never;
            }
            _ => {
                // memory ops
                error!("Invalid operation in a true op {}!", str_of_rule);
                return AsmTerm::Never;
            }
        }
        loop {
            if rule_children.peek().is_none() {
                break;
            }
            rule_children.next().unwrap();
            let operator = rule_children.next().unwrap().as_str();
            rule_children.next().unwrap();
            let child_value = handle_expr(rule_children.next().unwrap(), limits);
            match child_value {
                AsmTerm::Expr(e) => {
                    if operator == "*" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Mul(box expr, box e)),
                            None => {
                                error!("Unable to multiply register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "+" || operator == "off" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Add(box expr, box e)),
                            None => Some(e),
                        };
                        continue;
                    }
                    todo!("{}", operator);
                }
                AsmTerm::Never => {
                    error!("Propagating never across {}!", str_of_rule);
                    return AsmTerm::Never;
                }
                _ => {
                    // memory ops
                    error!("Invalid operation in an expr multiop {}!", str_of_rule);
                    return AsmTerm::Never;
                }
            }
        }
        if expr.is_some() {
            return AsmTerm::Expr(expr.unwrap());
        }
        // r.into_inner()
        todo!("{}", str_of_rule);
    }
    if rule.as_rule() == Rule::aexpr_multiop {
        let rule_children_vec = rule.into_inner().collect::<Vec<_>>();
        if rule_children_vec.len() == 1 {
            return handle_expr(rule_children_vec.into_iter().next().unwrap(), limits);
        }
        let mut rule_children = rule_children_vec.into_iter().peekable();
        let first_child_term = handle_expr(rule_children.next().unwrap(), limits);
        let mut reg: Option<Reg> = None;
        let mut expr: Option<Expr> = None;
        match first_child_term {
            AsmTerm::Reg(r) => {
                reg = Some(r);
            }
            AsmTerm::Expr(e) => {
                expr = Some(e);
            }
            AsmTerm::AddReg(a, b) => {
                reg = Some(b);
                expr = Some(a);
            }
            AsmTerm::Never => {
                error!("Propagating never across {}!", str_of_rule);
                return AsmTerm::Never;
            }
            _ => {
                // memory ops
                error!(
                    "Invalid memory operation in a true multiop {}!",
                    str_of_rule
                );
                return AsmTerm::Never;
            }
        }
        loop {
            if rule_children.peek().is_none() {
                break;
            }
            rule_children.next().unwrap();
            let operator = rule_children.next().unwrap().as_str();
            rule_children.next().unwrap();
            let child_term = handle_expr(rule_children.next().unwrap(), limits);
            match child_term {
                AsmTerm::Reg(r) => {
                    if operator != "+" && operator != "off" {
                        error!("Invalid operator at {}!", str_of_rule);
                        return AsmTerm::Never;
                    }
                    if reg.is_some() {
                        error!("Invalid duplicate register add at {}!", str_of_rule);
                        return AsmTerm::Never;
                    }
                    reg = Some(r);
                    continue;
                }
                AsmTerm::Expr(e) => {
                    if operator == "*" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Mul(box expr, box e)),
                            None => {
                                error!("Unable to multiply register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "+" || operator == "off" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Add(box expr, box e)),
                            None => Some(e),
                        };
                        continue;
                    }
                    todo!("{}", operator);
                }
                AsmTerm::AddReg(e, r) => {
                    if operator != "+" && operator != "off" {
                        error!("Invalid operator at {}!", str_of_rule);
                        return AsmTerm::Never;
                    }
                    if reg.is_some() {
                        error!("Invalid duplicate register add at {}!", str_of_rule);
                        return AsmTerm::Never;
                    }
                    reg = Some(r);
                    expr = match expr {
                        Some(expr) => Some(Expr::Add(box expr, box e)),
                        None => Some(e),
                    };
                    continue;
                }
                AsmTerm::Never => {
                    error!("Propagating never across {}!", str_of_rule);
                    return AsmTerm::Never;
                }
                _ => {
                    // memory ops
                    error!(
                        "Invalid memory operation in a true multiop {}!",
                        str_of_rule
                    );
                    return AsmTerm::Never;
                }
            }
        }
        if reg.is_some() && expr.is_none() {
            return AsmTerm::Reg(reg.unwrap());
        }
        if reg.is_some() && expr.is_some() {
            return AsmTerm::AddReg(expr.unwrap(), reg.unwrap());
        }
        if expr.is_some() {
            return AsmTerm::Expr(expr.unwrap());
        }
        // r.into_inner()
        todo!("{}", str_of_rule);
    }
    trace!("{:?}", rule.as_rule());
    todo!()
    // Resolvable::Bytes(vec![])
}

fn recurse_expand(e: Expr, hm: &HashMap<String, usize>) -> isize {
    match e {
        Expr::Label(lbl) => {
            (*hm.get(&lbl)
                .expect(&format!("Symbol {:?} does not exist", &lbl))) as isize
        }
        Expr::Number(num) => num as isize,
        Expr::Add(l, r) => recurse_expand(*l, hm) + recurse_expand(*r, hm),
        Expr::Sub(l, r) => recurse_expand(*l, hm) - recurse_expand(*r, hm),
        Expr::Div(l, r) => recurse_expand(*l, hm) / recurse_expand(*r, hm),
        Expr::Mul(l, r) => recurse_expand(*l, hm) * recurse_expand(*r, hm),
        Expr::Shl(l, r) => recurse_expand(*l, hm) << recurse_expand(*r, hm),
        Expr::Shr(l, r) => recurse_expand(*l, hm) >> recurse_expand(*r, hm),
    }
}

fn asmexpr_resolve(a: AsmTerm) -> Resolvable {
    match a {
        AsmTerm::Reg(r) => {
            return Resolvable::Bytes(vec![r.to_id()]);
        }
        AsmTerm::Expr(what) => {
            return Resolvable::Unresolved(
                box move |hm| {
                    let p: [&[u8]; 2] = [
                        &[0],
                        &(recurse_expand(what.clone(), hm) as u32).to_le_bytes(),
                    ];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadD(what) => {
            return Resolvable::Unresolved(
                box move |hm| {
                    fn recurse_expand(e: Expr, hm: &HashMap<String, usize>) -> isize {
                        match e {
                            Expr::Label(lbl) => (*hm.get(&lbl).unwrap()) as isize,
                            Expr::Number(num) => num as isize,
                            Expr::Add(l, r) => recurse_expand(*l, hm) + recurse_expand(*r, hm),
                            Expr::Sub(l, r) => recurse_expand(*l, hm) - recurse_expand(*r, hm),
                            Expr::Div(l, r) => recurse_expand(*l, hm) / recurse_expand(*r, hm),
                            Expr::Mul(l, r) => recurse_expand(*l, hm) * recurse_expand(*r, hm),
                            Expr::Shl(l, r) => recurse_expand(*l, hm) << recurse_expand(*r, hm),
                            Expr::Shr(l, r) => recurse_expand(*l, hm) >> recurse_expand(*r, hm),
                        }
                    }
                    let p: [&[u8]; 2] = [
                        &[0x03],
                        &(recurse_expand(what.clone(), hm) as u32).to_le_bytes(),
                    ];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadDRegoff(what, r) => {
            return Resolvable::Unresolved(
                box move |hm| {
                    let num = recurse_expand(what.clone(), hm);
                    let leb = num.abs().to_le_bytes();
                    let ono = if num < 0 { 4 } else { 0 };
                    let p: [&[u8]; 2] = [&[0x23 + ono, r.to_id()], &leb.split_at(3).0];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadDReg(r) => {
            return Resolvable::Unresolved(
                box move |_hm| {
                    let p: [&[u8]; 2] = [&[0x23, r.to_id()], &[0, 0, 0]];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::AddReg(_, _) => {}
        AsmTerm::Never => return Resolvable::Bytes(vec![]),
        #[allow(unreachable_patterns)]
        _ => {}
    }
    todo!("{:?}", a);
}

fn handle_line(rule: Pair<'_, Rule>) -> Resolvable {
    let inner = rule.into_inner();
    if inner.peek().is_none() {
        return Resolvable::Bytes(vec![]);
    }
    let target = inner.peek().unwrap();
    match target.as_rule() {
        Rule::forced_white_ln => {
            let mut target_inner = target.into_inner();
            target_inner.next();
            handle_line(target_inner.next().unwrap())
        }
        Rule::times_ln => {
            let mut target_inner = target.into_inner();
            let times_command = target_inner.next().unwrap();
            target_inner.next();
            let actual_command = target_inner.next().unwrap();
            let times_str = times_command.as_str();
            let i = if times_str.starts_with("x") {
                times_str.split_at(1).1.parse().unwrap()
            } else {
                let mut times_inside = times_command.clone().into_inner();
                times_inside.next();
                times_inside.next();
                times_inside.next().unwrap().as_str().parse().unwrap()
            };
            let (resolved_box, rsize, _) = into_unresolved(handle_line(actual_command));
            Resolvable::Unresolved(
                box move |hm| resolved_box(hm).repeat(i),
                rsize * i,
                HashMap::new(),
            )
        }
        Rule::label_ln => {
            let mut symbols = HashMap::new();
            let mut target_iter = target.into_inner();
            let label = target_iter.next().unwrap().as_str();
            symbols.insert(label.to_string().strip_suffix(":").unwrap().to_string(), 0);
            concat(
                Resolvable::Unresolved(box |_| vec![], 0, symbols),
                handle_line(target_iter.next().unwrap()),
            )
        }
        Rule::dw_ln => {
            let mut target_iter = target.into_inner();
            let dw_type = target_iter.next().unwrap().as_str();
            target_iter.next();
            let val = target_iter.next().unwrap();
            let val = match handle_expr(val, ExprUsageLimits::Int) {
                AsmTerm::Expr(e) => e,
                AsmTerm::Never => todo!("handle nevers here"),
                _ => unreachable!(),
            };
            let dw_type_box = dw_type.to_string().into_boxed_str();
            Resolvable::Unresolved(
                box move |hm| {
                    let v = recurse_expand(val.clone(), hm);
                    match dw_type_box.borrow() {
                        "dd" => (v as u32).to_le_bytes().iter().map(|e| *e).collect(),
                        "dw" => (v as u16).to_le_bytes().iter().map(|e| *e).collect(),
                        "db" => (v as u8).to_le_bytes().iter().map(|e| *e).collect(),
                        _ => todo!(),
                    }
                },
                match dw_type {
                    "dd" => 4,
                    "dw" => 2,
                    "db" => 1,
                    _ => unreachable!(),
                },
                HashMap::new(),
            )
        }
        Rule::mvmov_ln => {
            let target_str = target.as_str();
            let mut target_iter = target.into_inner();
            target_iter.next();
            target_iter.next();
            let lhs = target_iter.next().unwrap();
            target_iter.next();
            target_iter.next();
            let rhs = target_iter.next().unwrap();
            let lhs = into_unresolved(asmexpr_resolve(handle_expr(lhs, ExprUsageLimits::InsnLHS)));
            let rhs = into_unresolved(asmexpr_resolve(handle_expr(rhs, ExprUsageLimits::InsnRHS)));

            if lhs.1 + rhs.1 > 6 {
                error!("Instruction {} encodes to an opcode too large.", target_str);
                return Resolvable::Bytes(vec![]);
            }

            Resolvable::Unresolved(
                box move |symbols| {
                    let left = lhs.0(symbols);
                    let right = rhs.0(symbols);
                    let mut buf = vec![];
                    let mut buffer_writer = std::io::Cursor::new(&mut buf);
                    buffer_writer.write(&[0xf0]).unwrap();
                    buffer_writer.write(&left).unwrap();
                    buffer_writer.write(&right).unwrap();
                    for _i in 0..(8 - buffer_writer.position()) {
                        buffer_writer.write(&[0x0f]).unwrap();
                    }
                    drop(buffer_writer);
                    buf
                },
                8,
                HashMap::new(),
            )
        }
        unhandled_rule => todo!("{:?}", unhandled_rule),
    }
}

fn main() {
    pretty_env_logger::init();
    let app = App::new("sasm")
        .version("0.1.0")
        .author("pitust <piotr@stelmaszek.com>")
        .about("simu is an amazing assembler for simdisca")
        .arg(
            Arg::with_name("INPUT")
                .required(true)
                .help("Input File")
                .index(1),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .help("Output file")
                .default_value("out.bin"),
        )
        .arg(
            Arg::with_name("offset")
                .short("b")
                .help("Base address")
                .default_value("0xFFFFC000"),
        )
        .arg(
            Arg::with_name("outfmt")
                .short("f")
                .help("Output format")
                .default_value("bin"),
        );
    let matches = app.get_matches();
    let offset = parse_number(matches.value_of("offset").unwrap());
    let out = matches.value_of("output").unwrap();
    let outfmt = matches.value_of("outfmt").unwrap();
    let input = matches.value_of("INPUT").unwrap();
    let data = match std::fs::read_to_string(input) {
        Ok(ok) => ok,
        Err(e) => {
            error!("Unable to read file {}: {}", input, e);
            exit(0);
        }
    };
    let mut result = match <AsmParser as Parser<Rule>>::parse(Rule::grammar, &data) {
        Ok(a) => a,
        Err(a) => {
            println!("{}", a.with_path(input));
            exit(1);
        }
    };
    let mut current = Resolvable::Bytes(vec![]);
    for line in result.next().unwrap().into_inner() {
        if line.as_str() == "" {
            continue;
        }
        let lineresolvable = handle_line(line.into_inner().next().unwrap());
        current = concat(current, lineresolvable);
    }
    let (function, _, mut symbols) = into_unresolved(current);
    for symbol in symbols.iter_mut() {
        *symbol.1 += offset as usize;
    }
    let symbols = Box::leak(box symbols.clone());
    let data = function(symbols);
    drop(function);
    match outfmt {
        "bin" => {
            std::fs::write(out, data).unwrap();
        },
        "elf32" => {
            let mut elf = elf::ElfFile {
                FileHeader: elf::ElfFileHeader {
                    Class: format!("ELFCLASS32"),
                    Data: format!("ELFDATA2LSB"),
                    Type: format!("ET_EXEC"),
                    Machine: 0xeefe,
                    // todo: Entry
                    Entry: 0,
                },
                ProgramHeaders: vec![],
                Sections: vec![],
                Symbols: vec![],
            };
            // first, create a section
            elf.Sections.push(elf::ElfSection {
                Name: format!(".all"),
                Type: format!("SHT_PROGBITS"),
                Flags: ["SHF_ALLOC", "SHF_EXECINSTR", "SHF_WRITE"]
                    .iter()
                    .map(|e| e.to_string())
                    .collect(),
                Address: offset as usize,
                AddressAlign: 1,
                Content: hex::encode(data),
            });
            // then, write in all the symbols
            for symbol in symbols.iter() {
                elf.Symbols.push(elf::ElfSymbol {
                    Name: symbol.0.clone(),
                    Type: format!("STT_SECTION"),
                    Section: format!(".all"),
                    Value: *symbol.1,
                    Binding: Some(format!("STB_GLOBAL")),
                })
            }
            // then, create a program header
            elf.ProgramHeaders.push(elf::ElfProgramHeader {
                Align: 1,
                Flags: ["PF_X", "PF_R", "PF_W"]
                    .iter()
                    .map(|e| e.to_string())
                    .collect(),
                Sections: vec![elf::ElfSectionRef {
                    Section: format!(".all"),
                }],
                Type: format!("PT_LOAD"),
                VAddr: offset as usize
            });
            // and write it out!
            elf.to_disk("out.elf");
        }
        _ => unimplemented!("format {}", outfmt)
    }
}
