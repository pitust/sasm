#![feature(box_syntax)]
#![feature(unboxed_closures)]
#![feature(io_read_to_string)]
#![feature(option_expect_none)]
use clap::{App, Arg};
use log::{error, trace, warn};
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::{HashMap, HashSet},
    hash::Hash,
    io::Write,
};
use std::{process::exit, usize};

pub mod elf;

#[derive(Parser)]
#[grammar = "grammar.pest"] // relative to src
struct AsmParser;

thread_local! {
    pub static OFFSET: RefCell<isize> = RefCell::new(0);
    pub static START: RefCell<isize> = RefCell::new(0);
    pub static TMPSYMIDBASE: RefCell<isize> = RefCell::new(0);
    pub static DO_RELCODE: RefCell<bool> = RefCell::new(false);
    pub static GC_SYMS: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
}

fn tempsymid() -> String {
    TMPSYMIDBASE.with(|a| {
        let i = a.replace_with(|a| *a + 1);
        format!("___sym${}", i)
    })
}

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
    Or(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Current,
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
    LoadW(Expr),
    LoadB(Expr),
    LoadDRegoff(Expr, Reg),
    LoadWRegoff(Expr, Reg),
    LoadBRegoff(Expr, Reg),
    LoadDReg(Reg),
    LoadWReg(Reg),
    LoadBReg(Reg),
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
        if !limits.covers_int() {
            error!("Invalid Int-only operand {}!", str_of_rule);
            return AsmTerm::Never;
        }
        return AsmTerm::Expr(Expr::Label(str_of_rule.to_string()));
    }
    if rule.as_rule() == Rule::aexpr_rel {
        let mut rule_inner = rule.into_inner();
        if !limits.covers_lhs() {
            error!("Unable to use a relative offset {}!", str_of_rule);
            return AsmTerm::Never;
        }
        rule_inner.next();
        let id = rule_inner.next().unwrap().as_str();
        return AsmTerm::LoadDRegoff(
            Expr::Add(
                box Expr::Sub(box Expr::Number(0), box Expr::Current),
                box Expr::Label(format!("{}@got", id)),
            ),
            Reg::mrp,
        );
    }
    if rule.as_rule() == Rule::aexpr_deref {
        let mut rule_inner = rule.into_inner();
        let kind = rule_inner.next().unwrap().as_str();
        rule_inner.next().unwrap();
        return match handle_expr(rule_inner.next().unwrap(), ExprUsageLimits::InsnRHS) {
            AsmTerm::Expr(expr) => match kind {
                "d" => AsmTerm::LoadD(expr),
                "w" => AsmTerm::LoadW(expr),
                "b" => AsmTerm::LoadB(expr),
                _ => unreachable!(),
            },
            AsmTerm::AddReg(expr, reg) => match kind {
                "d" => AsmTerm::LoadDRegoff(expr, reg),
                "w" => AsmTerm::LoadWRegoff(expr, reg),
                "b" => AsmTerm::LoadBRegoff(expr, reg),
                _ => unreachable!(),
            },
            AsmTerm::Reg(reg) => match kind {
                "d" => AsmTerm::LoadDReg(reg),
                "w" => AsmTerm::LoadWReg(reg),
                "b" => AsmTerm::LoadBReg(reg),
                _ => unreachable!(),
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
                    if operator == "/" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Div(box expr, box e)),
                            None => {
                                error!("Unable to divide register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "^" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Xor(box expr, box e)),
                            None => {
                                error!("Unable to xor a register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "|" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Or(box expr, box e)),
                            None => {
                                error!("Unable to or a register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "&" {
                        expr = match expr {
                            Some(expr) => Some(Expr::And(box expr, box e)),
                            None => {
                                error!("Unable to and a register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == ">>" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Shl(box expr, box e)),
                            None => {
                                error!(
                                    "Unable to shift left a register by value at {}!",
                                    str_of_rule
                                );
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "<<" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Shr(box expr, box e)),
                            None => {
                                error!(
                                    "Unable to shift right a register by value at {}!",
                                    str_of_rule
                                );
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
                    if operator == "-" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Sub(box expr, box e)),
                            None => Some(e),
                        };
                        continue;
                    }
                    unreachable!()
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
        unreachable!()
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
                                error!(
                                    "Unable to multiply a register by value at {}!",
                                    str_of_rule
                                );
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "/" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Mul(box expr, box e)),
                            None => {
                                error!("Unable to divide a register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "&" {
                        expr = match expr {
                            Some(expr) => Some(Expr::And(box expr, box e)),
                            None => {
                                error!("Unable to and a register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "|" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Or(box expr, box e)),
                            None => {
                                error!("Unable to or a register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "^" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Xor(box expr, box e)),
                            None => {
                                error!("Unable to or a register by value at {}!", str_of_rule);
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == ">>" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Shr(box expr, box e)),
                            None => {
                                error!(
                                    "Unable to shift right a register by value at {}!",
                                    str_of_rule
                                );
                                return AsmTerm::Never;
                            }
                        };
                        continue;
                    }
                    if operator == "<<" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Shl(box expr, box e)),
                            None => {
                                error!(
                                    "Unable to shift left a register by value at {}!",
                                    str_of_rule
                                );
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
                    if operator == "-" {
                        expr = match expr {
                            Some(expr) => Some(Expr::Sub(box expr, box e)),
                            None => Some(e),
                        };
                        continue;
                    }
                    unreachable!()
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
        unreachable!()
    }
    trace!("{:?}", rule.as_rule());
    unreachable!()
}
fn outer_recurse(
    e: Expr,
    s: String,
) -> fn(e: Expr, hm: &HashMap<String, usize>, cur: isize) -> isize {
    GC_SYMS.with(move |a| {
        fn scan(e: Expr, s: &String, r: &RefCell<HashSet<String>>) {
            match e {
                Expr::Label(lbl) => {
                    let mut b = r.borrow_mut();
                    b.insert(lbl.clone());
                }
                Expr::Number(_) => {}
                Expr::Add(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Sub(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Div(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Mul(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Shl(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Shr(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Or(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Xor(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::And(a, b) => {
                    scan(*a.clone(), s, r);
                    scan(*b.clone(), s, r);
                }
                Expr::Current => {
                    let mut b = r.borrow_mut();
                    b.insert(s.clone());
                }
            }
        }
        scan(e, &s, a);
    });
    fn recurse_expand(e: Expr, hm: &HashMap<String, usize>, cur: isize) -> isize {
        match e {
            Expr::Label(lbl) => {
                (*hm.get(&lbl)
                    .expect(&format!("Symbol {:?} does not exist", &lbl))) as isize
            }
            Expr::Number(num) => num as isize,
            Expr::Add(l, r) => recurse_expand(*l, hm, cur) + recurse_expand(*r, hm, cur),
            Expr::Sub(l, r) => recurse_expand(*l, hm, cur) - recurse_expand(*r, hm, cur),
            Expr::Div(l, r) => recurse_expand(*l, hm, cur) / recurse_expand(*r, hm, cur),
            Expr::Mul(l, r) => recurse_expand(*l, hm, cur) * recurse_expand(*r, hm, cur),
            Expr::Shl(l, r) => recurse_expand(*l, hm, cur) << recurse_expand(*r, hm, cur),
            Expr::Shr(l, r) => recurse_expand(*l, hm, cur) >> recurse_expand(*r, hm, cur),
            Expr::And(l, r) => recurse_expand(*l, hm, cur) & recurse_expand(*r, hm, cur),
            Expr::Or(l, r) => recurse_expand(*l, hm, cur) | recurse_expand(*r, hm, cur),
            Expr::Xor(l, r) => recurse_expand(*l, hm, cur) ^ recurse_expand(*r, hm, cur),
            Expr::Current => cur,
        }
    }
    return recurse_expand;
}

fn asmexpr_resolve(a: AsmTerm, temp_sym: String) -> Resolvable {
    match a {
        AsmTerm::Reg(r) => {
            return Resolvable::Bytes(vec![r.to_id()]);
        }
        AsmTerm::Expr(what) => {
            let recurse_expand = outer_recurse(what.clone(), temp_sym.clone());
            return Resolvable::Unresolved(
                box move |hm| {
                    let p: [&[u8]; 2] = [
                        &[0],
                        &((recurse_expand(
                            what.clone(),
                            hm,
                            match hm.get(&temp_sym) {
                                Some(a) => *a,
                                None => 0,
                            } as isize,
                        ) as isize) as u32)
                            .to_le_bytes(),
                    ];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadD(what) => {
            let recurse_expand = outer_recurse(what.clone(), temp_sym.clone());
            return Resolvable::Unresolved(
                box move |hm| {
                    let p: [&[u8]; 2] = [
                        &[0x03],
                        &(recurse_expand(
                            what.clone(),
                            hm,
                            match hm.get(&temp_sym) {
                                Some(a) => *a,
                                None => 0,
                            } as isize,
                        ) as u32)
                            .to_le_bytes(),
                    ];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadDRegoff(what, r) => {
            let recurse_expand = outer_recurse(what.clone(), temp_sym.clone());
            return Resolvable::Unresolved(
                box move |hm| {
                    let num = recurse_expand(
                        what.clone(),
                        hm,
                        match hm.get(&temp_sym) {
                            Some(a) => *a,
                            None => 0,
                        } as isize,
                    );
                    let leb = (num.abs() as u32).to_le_bytes();
                    let ono = if num < 0 { 3 } else { 0 };
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
        AsmTerm::AddReg(_, _) => {
            error!("It is forbidden to create an expression in the form of register + number");
            return Resolvable::Bytes(vec![]);
        }
        AsmTerm::Never => return Resolvable::Bytes(vec![]),
        AsmTerm::LoadW(what) => {
            let recurse_expand = outer_recurse(what.clone(), temp_sym.clone());
            return Resolvable::Unresolved(
                box move |hm| {
                    let p: [&[u8]; 2] = [
                        &[0x02],
                        &(recurse_expand(
                            what.clone(),
                            hm,
                            match hm.get(&temp_sym) {
                                Some(a) => *a,
                                None => 0,
                            } as isize,
                        ) as u32)
                            .to_le_bytes(),
                    ];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadB(what) => {
            let recurse_expand = outer_recurse(what.clone(), temp_sym.clone());
            return Resolvable::Unresolved(
                box move |hm| {
                    let p: [&[u8]; 2] = [
                        &[0x01],
                        &(recurse_expand(
                            what.clone(),
                            hm,
                            match hm.get(&temp_sym) {
                                Some(a) => *a,
                                None => 0,
                            } as isize,
                        ) as u32)
                            .to_le_bytes(),
                    ];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadWRegoff(what, r) => {
            let recurse_expand = outer_recurse(what.clone(), temp_sym.clone());
            return Resolvable::Unresolved(
                box move |hm| {
                    let num = recurse_expand(
                        what.clone(),
                        hm,
                        match hm.get(&temp_sym) {
                            Some(a) => *a,
                            None => 0,
                        } as isize,
                    );
                    let leb = (num.abs() as u32).to_le_bytes();
                    let ono = if num < 0 { 3 } else { 0 };
                    let p: [&[u8]; 2] = [&[0x22 + ono, r.to_id()], &leb.split_at(3).0];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadBRegoff(what, r) => {
            let recurse_expand = outer_recurse(what.clone(), temp_sym.clone());
            return Resolvable::Unresolved(
                box move |hm| {
                    let num = recurse_expand(
                        what.clone(),
                        hm,
                        match hm.get(&temp_sym) {
                            Some(a) => *a,
                            None => 0,
                        } as isize,
                    );
                    let leb = num.abs().to_le_bytes();
                    let ono = if num < 0 { 3 } else { 0 };
                    let p: [&[u8]; 2] = [&[0x21 + ono, r.to_id()], &leb.split_at(3).0];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadWReg(r) => {
            return Resolvable::Unresolved(
                box move |_hm| {
                    let p: [&[u8]; 2] = [&[0x23, r.to_id()], &[0, 0, 0]];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
        AsmTerm::LoadBReg(r) => {
            return Resolvable::Unresolved(
                box move |_hm| {
                    let p: [&[u8]; 2] = [&[0x23, r.to_id()], &[0, 0, 0]];
                    p.iter().map(|e| *e).flatten().map(|e| *e).collect()
                },
                5,
                HashMap::new(),
            );
        }
    }
}

fn handle_line(rule: Pair<'_, Rule>) -> Resolvable {
    let str_of_rule = rule.as_str();
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
                AsmTerm::Never => {
                    error!("Unable to comply with a raw value store in this case");
                    return Resolvable::Bytes(vec![]);
                }
                _ => unreachable!(),
            };
            let dw_type_box = dw_type.to_string().into_boxed_str();
            let temp_sym = tempsymid();
            let temp_sym_cl = temp_sym.clone();
            let recurse_expand = outer_recurse(val.clone(), temp_sym.clone());
            Resolvable::Unresolved(
                box move |hm| {
                    let v = recurse_expand(
                        val.clone(),
                        hm,
                        match hm.get(&temp_sym) {
                            Some(a) => *a,
                            None => 0,
                        } as isize,
                    );
                    match dw_type_box.borrow() {
                        "dd" => (v as u32).to_le_bytes().iter().map(|e| *e).collect(),
                        "dw" => (v as u16).to_le_bytes().iter().map(|e| *e).collect(),
                        "db" => (v as u8).to_le_bytes().iter().map(|e| *e).collect(),
                        _ => unreachable!(),
                    }
                },
                match dw_type {
                    "dd" => 4,
                    "dw" => 2,
                    "db" => 1,
                    _ => unreachable!(),
                },
                {
                    let mut hm = HashMap::new();
                    hm.insert(temp_sym_cl, 0);
                    hm
                },
            )
        }
        Rule::entry_ln => {
            let mut target_iter = target.into_inner();
            target_iter.next();
            let val = target_iter.next().unwrap();
            let val = match handle_expr(val, ExprUsageLimits::Int) {
                AsmTerm::Expr(e) => e,
                AsmTerm::Never => {
                    error!("Unable to comply with a raw value store in this case");
                    return Resolvable::Bytes(vec![]);
                }
                _ => unreachable!(),
            };
            let recurse_expand = outer_recurse(val.clone(), "_$fake".to_string());
            Resolvable::Unresolved(
                box move |hm| {
                    let start = recurse_expand(val.clone(), hm, 0);
                    START.with(|start_refcell| {
                        start_refcell.replace(start);
                    });
                    vec![]
                },
                0,
                HashMap::new(),
            )
        }
        Rule::offset_ln => {
            let mut target_inner = target.into_inner();
            target_inner.next();
            let expr = match handle_expr(target_inner.next().unwrap(), ExprUsageLimits::Int) {
                AsmTerm::Expr(e) => e,
                AsmTerm::Never => {
                    error!("Unable to set the offset");
                    return Resolvable::Bytes(vec![]);
                }
                _ => {
                    error!("Prohibited syntax in `-off`");
                    return Resolvable::Bytes(vec![]);
                }
            };
            let recurse_expand = outer_recurse(expr.clone(), "_$fake".to_string());
            let new_base = recurse_expand(expr, &HashMap::new(), 0);

            OFFSET.with(|offset_refcell| {
                offset_refcell.replace(new_base);
            });

            Resolvable::Bytes(vec![])
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
            let tmpsym = tempsymid();
            let lhs = into_unresolved(asmexpr_resolve(
                handle_expr(lhs, ExprUsageLimits::InsnLHS),
                tmpsym.clone(),
            ));
            let rhs = into_unresolved(asmexpr_resolve(
                handle_expr(rhs, ExprUsageLimits::InsnRHS),
                tmpsym.clone(),
            ));

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
                {
                    let mut hm = HashMap::new();
                    hm.insert(tmpsym, 0);
                    hm
                },
            )
        }
        Rule::as_cmd_ln => {
            match str_of_rule {
                "@init_dyn" => {
                    // initialize the GOT/PLT
                    // this actually jumps to a hidden bit of code in the GOT
                    // so it's real hacky
                    let mut hmm = HashMap::new();
                    hmm.insert("__got_after_fix_jumpback".to_string(), 8);
                    GC_SYMS.with(|a| {
                        let mut m = a.borrow_mut();
                        m.insert("__got_after_fix_jumpback".to_string());
                        m.insert("__got_fix_jump".to_string());
                    });
                    Resolvable::Unresolved(
                        box |hm| {
                            let mut buf = vec![];
                            let mut wr = std::io::Cursor::new(&mut buf);
                            wr.write(&[0xf0, 0x20, 0x00]).unwrap();
                            wr.write(
                                &(*hm.get(&"__got_fix_jump".to_string()).unwrap() as u32)
                                    .to_le_bytes(),
                            )
                            .unwrap();
                            wr.write(&[0x0f]).unwrap();
                            drop(wr);
                            buf
                        },
                        8,
                        hmm,
                    )
                }
                "-relcode" => {
                    DO_RELCODE.with(|a| a.replace(true));
                    Resolvable::Bytes(vec![])
                }
                _ => unreachable!(),
            }
        }
        rule => {
            trace!("{:?}", rule);
            unreachable!()
        }
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
                .default_value("0xdeadbeef"),
        )
        .arg(
            Arg::with_name("outfmt")
                .short("f")
                .help("Output format")
                .default_value("bin"),
        );
    let matches = app.get_matches();
    let offset = parse_number(matches.value_of("offset").unwrap());
    OFFSET.with(|a| {
        a.replace(offset);
    });
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
    if DO_RELCODE.with(|a| *a.borrow()) {
        warn!("PIC doesn't really work...");
        let mut hmm = HashMap::new();
        hmm.insert("__got_fix_jump".to_string(), 0);
        hmm.insert("__got".to_string(), 8);
        // __got_after_fix_jumpback
        current = concat(
            current,
            Resolvable::Unresolved(
                box |hm| {
                    let mut buf = vec![];
                    let mut wr = std::io::Cursor::new(&mut buf);
                    let got_fix_jump: usize = *hm.get(&"__got_fix_jump".to_string()).unwrap();
                    let got = got_fix_jump + 8;
                    wr.write(&[0xf0, 0x20, 0x00]).unwrap();
                    wr.write(
                        &((hm.get(&"__got_fix_jump".to_string()).unwrap() + (hm.len()) * 4) as u32)
                            .to_le_bytes(),
                    )
                    .unwrap();
                    wr.write(&[0x0f]).unwrap();

                    let mut revershm: HashMap<usize, String> = HashMap::new();

                    let mut gotsymcount = 0;

                    for label in hm {
                        if label.0.ends_with("@got") {
                            revershm.insert(gotsymcount, label.0.clone());
                            gotsymcount += 1;
                        }
                    }
                    for i in 0..gotsymcount {
                        let sym = revershm.get(&i).unwrap();
                        let o: usize = 0x1_0000_0000
                            + *hm.get(&sym.split_at(sym.len() - 4).0.to_string()).unwrap();
                        println!("{:?} {} {:#x?} {:#x?}", revershm, gotsymcount, o, got);
                        let symval: usize = o - gotsymcount * 4 - got;

                        wr.write(&(symval as u32).to_le_bytes()).unwrap();
                    }

                    wr.write(&[0xf0, Reg::orl.to_id(), Reg::mrp.to_id(), 0, 0, 0, 0, 0x0f])
                        .unwrap();

                    for i in 0..gotsymcount {
                        let calced_readoff = 0x1_0000_0000
                            - (0x1_0000_0000 + (got + i * 4) - (got + gotsymcount * 20))
                            & 0xffff_ffff;
                        let calced_writeoff = 0x1_0000_0000
                            - (0x1_0000_0000 + (got + i * 4) - (got + gotsymcount * 20 + 8))
                            & 0xffff_ffff;
                        wr.write(&[0xf0, Reg::orr.to_id(), 0x26, Reg::mrp.to_id()])
                            .unwrap();
                        wr.write(&(calced_readoff as u32).to_le_bytes().split_at(3).0)
                            .unwrap();
                        wr.write(&[0x0f]).unwrap();
                        wr.write(&[0xf0, 0x26, Reg::mrp.to_id()]).unwrap();
                        wr.write(&(calced_writeoff as u32).to_le_bytes().split_at(3).0)
                            .unwrap();
                        wr.write(&[Reg::ara.to_id(), 0x0f]).unwrap();
                    }

                    wr.write(&[0xf0, 0x20, 0x00]).unwrap();
                    wr.write(
                        &hm.get(&"__got_after_fix_jumpback".to_string())
                            .unwrap()
                            .to_le_bytes(),
                    )
                    .unwrap();
                    wr.write(&[0x0f]).unwrap();
                    drop(wr);
                    buf
                },
                0,
                hmm,
            ),
        )
    }
    let (function, _, mut symbols) = into_unresolved(current);
    let offset = OFFSET.with(|a| *a.borrow());
    if DO_RELCODE.with(|a| *a.borrow()) {
        let gfj_loc = *symbols.get(&format!("__got")).unwrap();
        let mut htmp = vec![];
        let mut offsets = 0;
        for symbol in symbols.iter() {
            if !symbol.0.ends_with("@got") {
                htmp.push((format!("{}@got", symbol.0), gfj_loc + offsets));
                offsets += 4;
            }
        }
        for e in htmp {
            symbols.insert(e.0, e.1);
        }
    }
    for symbol in symbols.iter_mut() {
        *symbol.1 += offset as usize;
    }
    GC_SYMS.with(|a| {
        let ab = a.borrow();
        let mut tbd = vec![];
        for k in symbols.iter_mut() {
            if ab.get(k.0).is_none() {
                tbd.push(k.0.clone());
            }
        }
        for k in tbd {
            symbols.remove(&k).unwrap();
        }
    });
    let symbols = Box::leak(box symbols.clone());
    let data = function(symbols);
    drop(function);
    match outfmt {
        "bin" => {
            std::fs::write(out, data).unwrap();
        }
        "elf32" => {
            let mut elf = elf::ElfFile {
                FileHeader: elf::ElfFileHeader {
                    Class: format!("ELFCLASS32"),
                    Data: format!("ELFDATA2LSB"),
                    Type: format!("ET_EXEC"),
                    Machine: 0xeefe,
                    Entry: START.with(|a| a.take() as usize),
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
                    Type: format!("STT_FUNC"),
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
                VAddr: offset as usize,
            });
            // and write it out!
            elf.to_disk("out.elf");
        }
        _ => unimplemented!("format {}", outfmt),
    }
}
