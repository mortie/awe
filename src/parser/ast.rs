#![allow(dead_code)]

use std::rc::Rc;

pub type Ident = Rc<String>;

pub type QualifiedIdent = Vec<Ident>;

#[derive(Debug, Clone)]
pub enum TypeParam {
    Type(Box<TypeSpec>),
}

#[derive(Debug, Clone)]
pub struct TypeSpec {
    pub ident: QualifiedIdent,
    pub params: Vec<TypeParam>,
}

#[derive(Debug, Clone)]
pub struct StructLiteral {
    pub typ: TypeSpec,
    pub initializers: Vec<FieldInitializer>,
}

#[derive(Debug, Clone)]
pub enum IntegerSize {
    Byte,
    Short,
    UShort,
    Int,
    UInt,
    Long,
    ULong,
}

#[derive(Debug, Clone)]
pub struct IntegerLiteral {
    pub num: i128,
    pub size: Option<IntegerSize>,
}

#[derive(Debug, Clone)]
pub enum LiteralExpr {
    Struct(StructLiteral),
    Integer(IntegerLiteral),
    String(Rc<String>),
    Bool(bool),
}

#[derive(Debug, Clone)]
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
    Gt,
    Geq,
}

#[derive(Debug, Clone)]
pub enum Locator {
    MemberAccess(Ident),
}

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(LiteralExpr),
    FuncCall(QualifiedIdent, Vec<Expression>),
    Cast(TypeSpec, Box<Expression>),
    Assignment(Ident, Vec<Locator>, Box<Expression>),
    Uninitialized(Option<TypeSpec>),
    Variable(Ident),
    Group(Box<Expression>),
    BinOp(Box<Expression>, BinOp, Box<Expression>),
    Reference(Box<Expression>),
    MemberAccess(Box<Expression>, Ident),
}

#[derive(Debug, Clone)]
pub enum Statement {
    If(Box<Expression>, Box<Statement>, Option<Box<Statement>>),
    Loop(Box<Statement>),
    Return(Option<Box<Expression>>),
    Break,
    TypeAlias(Ident, TypeSpec),
    DebugPrint(Box<Expression>),
    VarDecl(Ident, Box<Expression>),
    Block(Block),
    Debugger,
    Expression(Box<Expression>),
}

pub type Block = Vec<Statement>;

#[derive(Debug, Clone)]
pub struct FieldInitializer {
    pub name: Ident,
    pub expr: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: Ident,
    pub typ: TypeSpec,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: Ident,
    pub fields: Vec<FieldDecl>,
    pub type_params: Vec<Ident>,
}

#[derive(Debug, Clone)]
pub struct FuncSignature {
    pub ident: QualifiedIdent,
    pub params: Vec<FieldDecl>,
    pub ret: TypeSpec,
}

#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub signature: FuncSignature,
    pub body: Block,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Struct(StructDecl),
    Func(FuncDecl),
    ExternFunc(FuncSignature),
}

pub type Program = Vec<Declaration>;
