#![allow(dead_code)]

use std::rc::Rc;

pub type Ident = Rc<String>;

pub type QualifiedIdent = Vec<Ident>;

#[derive(Debug)]
pub enum TypeParam {
    Type(Box<TypeSpec>),
}

#[derive(Debug)]
pub struct TypeSpec {
    pub ident: QualifiedIdent,
    pub params: Vec<TypeParam>,
}

#[derive(Debug)]
pub enum Expression {
    FuncCall(QualifiedIdent, Vec<Expression>),
    Assignment(Ident, Box<Expression>),
    Uninitialized(Option<TypeSpec>),
    Variable(Ident),
    Group(Box<Expression>),
}

#[derive(Debug)]
pub enum Statement {
    Expression(Box<Expression>),
    VarDecl(Ident, Box<Expression>),
    Return(Option<Box<Expression>>),
}

pub type Block = Vec<Statement>;

#[derive(Debug)]
pub struct FieldDecl {
    pub name: Ident,
    pub typ: TypeSpec,
}

#[derive(Debug)]
pub struct StructDecl {
    pub name: Ident,
    pub fields: Vec<FieldDecl>,
}

#[derive(Debug)]
pub struct FuncSignature {
    pub ident: QualifiedIdent,
    pub params: Vec<FieldDecl>,
    pub ret: TypeSpec,
}

#[derive(Debug)]
pub struct FuncDecl {
    pub signature: FuncSignature,
    pub body: Block,
}

#[derive(Debug)]
pub enum Declaration {
    Struct(StructDecl),
    Func(FuncDecl),
    ExternFunc(FuncSignature),
}

pub type Program = Vec<Declaration>;
