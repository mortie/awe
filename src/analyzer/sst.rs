#![allow(dead_code)]

use std::{collections::HashMap, rc::Rc};

#[derive(Debug, Clone)]
pub struct LocalVar {
    pub typ: Rc<Type>,
    pub frame_offset: isize,
}

#[derive(Debug, Copy, Clone)]
pub enum Primitive {
    Void,
    Int,
    UInt,
    Float,
}

#[derive(Debug)]
pub enum TypeKind {
    Primitive(Primitive),
    Pointer(Rc<Type>),
    Struct(Rc<Struct>),
}

#[derive(Debug)]
pub struct Type {
    pub name: Rc<String>,
    pub size: usize,
    pub align: usize,
    pub kind: TypeKind,
}

#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: Rc<String>,
    pub typ: Rc<Type>,
    pub offset: usize,
}

#[derive(Debug)]
pub struct FieldDecls {
    pub fields: Vec<FieldDecl>,
    pub size: usize,
    pub align: usize,
}

#[derive(Debug)]
pub struct Struct {
    pub name: Rc<String>,
    pub fields: Vec<FieldDecl>,
    pub methods: HashMap<Rc<String>, Rc<Function>>,
}

impl Struct {
    pub fn field(&self, name: &str) -> Option<FieldDecl> {
        for field in &self.fields {
            if field.name.as_str() == name {
                return Some(field.clone());
            }
        }

        None
    }
}

#[derive(Debug)]
pub struct FuncSignature {
    pub name: Rc<String>,
    pub params: FieldDecls,
    pub ret: Rc<Type>,
}

#[derive(Debug)]
pub struct Function {
    pub signature: Rc<FuncSignature>,
    pub body: Vec<Statement>,
    pub return_addr: Rc<LocalVar>,
    pub return_var: Rc<LocalVar>,
    pub stack_size: usize,
    pub always_returns: bool,
    pub is_leaf: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct StringConstant {
    pub index: u32,
}

#[derive(Debug)]
pub enum Literal {
    Struct(Rc<Struct>, Vec<Expression>),
    Integer(i128),
    String(StringConstant),
    Bool(bool),
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    Eq,
    Neq,
    Lt,
    Leq,
}

#[derive(Debug)]
pub enum Locator {
    MemberAccess(FieldDecl),
}

#[derive(Debug)]
pub enum ExprKind {
    Literal(Literal),
    FuncCall(Rc<FuncSignature>, Vec<Expression>),
    Cast(Box<Expression>),
    Assignment(Rc<LocalVar>, Vec<Locator>, Box<Expression>),
    Uninitialized,
    Variable(Rc<LocalVar>),
    BinOp(Box<Expression>, BinOp, Box<Expression>),
    Reference(Box<Expression>),
    MemberAccess(Box<Expression>, FieldDecl),
}

#[derive(Debug)]
pub struct Expression {
    pub typ: Rc<Type>,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub enum Statement {
    If(Box<Expression>, Box<Statement>, Box<Statement>),
    Loop(Box<Statement>),
    Return(Option<Box<Expression>>),
    Break,
    VarDecl(Rc<LocalVar>, Box<Expression>),
    Block(Vec<Statement>),
    Debugger,
    Expression(Box<Expression>),
    Empty,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Type(Rc<Type>),
    Function(Rc<Function>),
    ExternFunc(Rc<FuncSignature>),
}

#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Rc<Function>>,
    pub strings: Vec<(StringConstant, Rc<String>)>,
}
