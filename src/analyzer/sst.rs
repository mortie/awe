use std::{collections::HashMap, rc::Rc};

#[derive(Debug)]
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
    Integer(i128),
    String(StringConstant),
    Bool(bool),
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Leq,
}

#[derive(Debug)]
pub enum ExprKind {
    Literal(Literal),
    FuncCall(Rc<FuncSignature>, Vec<Expression>),
    Assignment(Rc<LocalVar>, Box<Expression>),
    Uninitialized,
    Variable(Rc<LocalVar>),
    BinOp(Box<Expression>, BinOp, Box<Expression>),
}

#[derive(Debug)]
pub struct Expression {
    pub typ: Rc<Type>,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub enum Statement {
    If(Box<Expression>, Box<Statement>, Box<Statement>),
    Return(Option<Box<Expression>>),
    VarDecl(Rc<LocalVar>, Box<Expression>),
    Block(Vec<Statement>),
    Expression(Box<Expression>),
    Empty,
}

#[derive(Debug)]
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
