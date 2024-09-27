use std::{collections::HashMap, rc::Rc};

#[derive(Debug)]
pub struct LocalVar {
    pub typ: Rc<Type>,
    pub frame_offset: isize,
}

#[derive(Debug)]
pub enum Primitive {
    Void,
    Int,
    UInt,
    Float,
    ReturnAddr,
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

#[derive(Debug)]
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
    pub fields: HashMap<Rc<String>, FieldDecl>,
    pub methods: HashMap<Rc<String>, Rc<Function>>,
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
    pub stack_size: usize,
}

#[derive(Debug)]
pub enum ExprKind {
    FuncCall(Rc<FuncSignature>, Vec<Expression>),
    Assignment(Rc<LocalVar>, Box<Expression>),
    Uninitialized,
    Variable(Rc<LocalVar>),
}

#[derive(Debug)]
pub struct Expression {
    pub typ: Rc<Type>,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub enum Statement {
    Expression(Box<Expression>),
    VarDecl(Rc<LocalVar>, Box<Expression>),
}

#[derive(Debug)]
pub enum Declaration {
    Type(Rc<Type>),
    Function(Rc<Function>),
    ExternFunc(Rc<FuncSignature>)
}
