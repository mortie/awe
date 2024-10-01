use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::sst;
use crate::parser::ast;

#[derive(Debug)]
pub enum AnalysisError {
    UndeclaredVariable(Rc<String>),
    UndeclaredType(Rc<String>),
    UndeclaredFunction(Rc<String>),
    MultipleDefinitions(Rc<String>),
    TypeConflict(Rc<sst::Type>, Rc<sst::Type>),
    InconclusiveInference,
    BadParamCount(usize, usize),
    BadIntegerLiteral(i128),
    BadTypeParameters,
    NonVoidFunctionMustReturn,
    FunctionCtx(Rc<String>, Box<AnalysisError>),

    // Unimplemented is for code that's a work in progress.
    // Most of the time, nothing which uses Unimplemented will be committed,
    // so it should always be allowed to be unused.
    #[allow(dead_code)]
    Unimplemented,
}

type Result<T> = std::result::Result<T, AnalysisError>;

struct ScopeProps {
    always_returns: bool,
    is_leaf: bool,
}

impl ScopeProps {
    fn new() -> Self {
        Self {
            always_returns: false,
            is_leaf: true,
        }
    }
}

struct Scope<'a> {
    frame: Rc<RefCell<StackFrame<'a>>>,
    parent: Option<Rc<Scope<'a>>>,
    vars: RefCell<HashMap<Rc<String>, Rc<sst::LocalVar>>>,
    types: RefCell<HashMap<Rc<String>, Rc<sst::Type>>>,
    offset: RefCell<usize>,
    props: RefCell<ScopeProps>,
}

impl<'a> Scope<'a> {
    fn new(frame: Rc<RefCell<StackFrame<'a>>>) -> Rc<Self> {
        Rc::new(Self {
            frame,
            parent: None,
            vars: RefCell::new(HashMap::new()),
            types: RefCell::new(HashMap::new()),
            offset: RefCell::new(0),
            props: RefCell::new(ScopeProps::new()),
        })
    }

    fn from_parent(parent: Rc<Scope<'a>>) -> Rc<Self> {
        Rc::new(Self {
            frame: parent.frame.clone(),
            parent: Some(parent),
            vars: RefCell::new(HashMap::new()),
            types: RefCell::new(HashMap::new()),
            offset: RefCell::new(0),
            props: RefCell::new(ScopeProps::new()),
        })
    }

    fn maybe_lookup(&self, name: Rc<String>) -> Option<Rc<sst::LocalVar>> {
        if let Some(var) = self.vars.borrow().get(&name) {
            return Some(var.clone());
        }

        if let Some(parent) = &self.parent {
            return parent.maybe_lookup(name);
        }

        None
    }

    fn lookup(&self, name: Rc<String>) -> Result<Rc<sst::LocalVar>> {
        match self.maybe_lookup(name.clone()) {
            Some(var) => Ok(var),
            None => Err(AnalysisError::UndeclaredVariable(name)),
        }
    }

    fn declare(&self, name: Rc<String>, typ: Rc<sst::Type>) -> Result<Rc<sst::LocalVar>> {
        let mut vars = self.vars.borrow_mut();
        if vars.contains_key(&name) {
            return Err(AnalysisError::MultipleDefinitions(name));
        }

        let mut offset = self.offset.borrow_mut();
        while typ.size > 0 && *offset % typ.size != 0 {
            *offset += 1;
        }

        let size = typ.size;
        let var = Rc::new(sst::LocalVar {
            typ,
            frame_offset: *offset as isize,
        });

        *offset += size;
        if *offset > self.frame.borrow().size {
            self.frame.borrow_mut().size = *offset;
        }

        if name.as_str() != "_" {
            vars.insert(name, var.clone());
        }

        Ok(var)
    }

    fn declare_type_alias(&self, name: Rc<String>, typ: Rc<sst::Type>) -> Result<()> {
        let mut types = self.types.borrow_mut();
        if types.contains_key(&name) {
            return Err(AnalysisError::MultipleDefinitions(name));
        }

        types.insert(name, typ);
        Ok(())
    }

    fn get_type_alias(&self, name: &Rc<String>) -> Option<Rc<sst::Type>> {
        if let Some(typ) = self.types.borrow().get(name) {
            return Some(typ.clone());
        };

        if let Some(parent) = &self.parent {
            parent.get_type_alias(name)
        } else {
            None
        }
    }

    fn get_type(&self, spec: &ast::TypeSpec) -> Result<Rc<sst::Type>> {
        get_type(self.frame.borrow_mut().ctx, spec, Some(&self))
    }

    fn get_func_sig(&self, ident: &ast::QualifiedIdent) -> Result<Rc<sst::FuncSignature>> {
        let name = ident_to_name(ident);
        let frame = self.frame.borrow();
        let Some(decl) = frame.ctx.decls.get(&name) else {
            return Err(AnalysisError::UndeclaredFunction(name));
        };

        match decl {
            sst::Declaration::Function(func) => Ok(func.signature.clone()),
            sst::Declaration::ExternFunc(sig) => Ok(sig.clone()),
            _ => Err(AnalysisError::UndeclaredFunction(name)),
        }
    }
}

struct StackFrame<'a> {
    ctx: &'a mut Context,
    size: usize,
    ret: Rc<sst::Type>,
}

impl<'a> StackFrame<'a> {
    fn new(ctx: &'a mut Context, ret: Rc<sst::Type>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self { ctx, size: 0, ret }))
    }
}

struct Types {
    void: Rc<sst::Type>,
    bool: Rc<sst::Type>,
    byte: Rc<sst::Type>,
    short: Rc<sst::Type>,
    ushort: Rc<sst::Type>,
    int: Rc<sst::Type>,
    uint: Rc<sst::Type>,
    long: Rc<sst::Type>,
    ulong: Rc<sst::Type>,
    float: Rc<sst::Type>,
    double: Rc<sst::Type>,
    voidptr: Rc<sst::Type>,
}

struct Context {
    decls: HashMap<Rc<String>, sst::Declaration>,
    underscore: Rc<String>,
    types: Types,
    string_constant_map: HashMap<Rc<String>, sst::StringConstant>,
    string_constants: Vec<(sst::StringConstant, Rc<String>)>,
}

impl Context {
    fn new(types: Types) -> Self {
        let mut ctx = Self {
            decls: HashMap::new(),
            underscore: Rc::new("_".to_owned()),
            types,
            string_constant_map: HashMap::new(),
            string_constants: Vec::new(),
        };

        ctx.add_type(ctx.types.void.clone());
        ctx.add_type(ctx.types.byte.clone());
        ctx.add_type(ctx.types.bool.clone());
        ctx.add_type(ctx.types.short.clone());
        ctx.add_type(ctx.types.ushort.clone());
        ctx.add_type(ctx.types.int.clone());
        ctx.add_type(ctx.types.uint.clone());
        ctx.add_type(ctx.types.long.clone());
        ctx.add_type(ctx.types.ulong.clone());
        ctx.add_type(ctx.types.float.clone());
        ctx.add_type(ctx.types.double.clone());
        ctx.add_type(ctx.types.voidptr.clone());

        ctx
    }

    fn add_type(&mut self, typ: Rc<sst::Type>) {
        self.decls
            .insert(typ.name.clone(), sst::Declaration::Type(typ));
    }

    fn add_string(&mut self, str: Rc<String>) -> sst::StringConstant {
        if let Some(sc) = self.string_constant_map.get(&str) {
            return *sc;
        }

        let sc = sst::StringConstant {
            index: self.string_constants.len() as u32,
        };
        self.string_constant_map.insert(str.clone(), sc);
        self.string_constants.push((sc, str));
        sc
    }
}

fn ident_to_name(ident: &ast::QualifiedIdent) -> Rc<String> {
    if ident.len() == 0 {
        eprintln!("Zero-length ident! Treating as '_'");
        return Rc::new("_".to_owned());
    }

    if ident.len() == 1 {
        return ident[0].clone();
    }

    let mut name = String::new();
    for part in ident {
        if name != "" {
            name += "::";
        }
        name += part;
    }

    Rc::new(name)
}

fn get_type(
    ctx: &mut Context,
    spec: &ast::TypeSpec,
    scope: Option<&Scope>,
) -> Result<Rc<sst::Type>> {
    let ident = ident_to_name(&spec.ident);

    if ident.as_str() == "ptr" {
        if spec.params.len() != 1 {
            return Err(AnalysisError::BadTypeParameters);
        }

        let ast::TypeParam::Type(typ) = &spec.params[0];
        let typ = get_type(ctx, typ, scope)?;
        return Ok(make_pointer_to(ctx, typ));
    }

    if spec.params.len() == 0 {
        if let Some(typ) = scope.and_then(|scope| scope.get_type_alias(&ident)) {
            return Ok(typ);
        }

        if let Some(decl) = ctx.decls.get(&ident) {
            if let sst::Declaration::Type(typ) = decl {
                return Ok(typ.clone());
            }
        }

        return Err(AnalysisError::UndeclaredType(ident));
    }

    // TODO: Support type templates

    return Err(AnalysisError::UndeclaredType(ident));
}

fn make_pointer_to(ctx: &mut Context, typ: Rc<sst::Type>) -> Rc<sst::Type> {
    let name = Rc::new(format!("ptr[{}]", typ.name));
    if let Some(decl) = &ctx.decls.get(&name) {
        if let sst::Declaration::Type(typ) = decl {
            return typ.clone();
        }
    }

    let ptr = Rc::new(sst::Type {
        name: name.clone(),
        size: 8,
        align: 8,
        kind: sst::TypeKind::Pointer(typ),
    });
    ctx.decls.insert(name, sst::Declaration::Type(ptr.clone()));
    ptr
}

fn analyze_field_decls(
    ctx: &mut Context,
    field_decls: &[ast::FieldDecl],
    scope: Option<&Scope>,
) -> Result<sst::FieldDecls> {
    let mut names = HashSet::<Rc<String>>::new();
    let mut fields = Vec::<sst::FieldDecl>::new();
    let mut offset: usize = 0;
    let mut biggest_align: usize = 0;
    for decl in field_decls {
        let fname = decl.name.clone();
        let typ = get_type(ctx, &decl.typ, scope)?;

        if fname.as_str() != "_" && names.contains(&fname) {
            return Err(AnalysisError::MultipleDefinitions(fname));
        }

        let align = typ.align;
        while align != 0 && offset % align != 0 {
            offset += 1;
        }

        if align > biggest_align {
            biggest_align = align;
        }

        let size = typ.size;
        names.insert(fname.clone());
        fields.push(sst::FieldDecl {
            name: fname,
            typ,
            offset,
        });
        offset += size;
    }

    while biggest_align > 0 && offset % biggest_align != 0 {
        offset += 1;
    }

    Ok(sst::FieldDecls {
        fields,
        size: offset,
        align: biggest_align,
    })
}

fn analyze_struct_decl(ctx: &mut Context, sd: &ast::StructDecl) -> Result<()> {
    let name = sd.name.clone();
    if ctx.decls.contains_key(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    let info = analyze_field_decls(ctx, &sd.fields, None)?;

    let mut fields = HashMap::<Rc<String>, sst::FieldDecl>::new();
    for field in info.fields {
        fields.insert(field.name.clone(), field);
    }

    let typ = Rc::new(sst::Type {
        name: name.clone(),
        size: info.size,
        align: info.align,
        kind: sst::TypeKind::Struct(Rc::new(sst::Struct {
            name: name.clone(),
            fields,
            methods: HashMap::new(),
        })),
    });

    ctx.decls.insert(name, sst::Declaration::Type(typ));
    Ok(())
}

fn appropriate_int_type_for_num(types: &Types, num: i128) -> Result<Rc<sst::Type>> {
    if num > i64::MAX as i128 || num < i64::MIN as i128 {
        Err(AnalysisError::BadIntegerLiteral(num))
    } else if num > i32::MAX as i128 || num < i32::MIN as i128 {
        Ok(types.long.clone())
    } else {
        Ok(types.int.clone())
    }
}

fn analyze_literal(
    scope: Rc<Scope>,
    literal: &ast::LiteralExpr,
    inferred: Option<Rc<sst::Type>>,
) -> Result<sst::Expression> {
    match literal {
        ast::LiteralExpr::Integer(literal) => {
            let frame = scope.frame.borrow();
            let types = &frame.ctx.types;
            let typ = match literal.size {
                Some(ast::IntegerSize::Byte) => types.byte.clone(),
                Some(ast::IntegerSize::Short) => types.short.clone(),
                Some(ast::IntegerSize::UShort) => types.ushort.clone(),
                Some(ast::IntegerSize::Int) => types.int.clone(),
                Some(ast::IntegerSize::UInt) => types.uint.clone(),
                Some(ast::IntegerSize::Long) => types.long.clone(),
                Some(ast::IntegerSize::ULong) => types.ulong.clone(),
                None => match inferred {
                    Some(inferred) => inferred.clone(),
                    None => appropriate_int_type_for_num(types, literal.num)?,
                },
            };

            let (min, max) = if Rc::ptr_eq(&typ, &types.byte) {
                (u8::MIN as i128, u8::MAX as i128)
            } else if Rc::ptr_eq(&typ, &types.short) {
                (i16::MIN as i128, i16::MAX as i128)
            } else if Rc::ptr_eq(&typ, &types.ushort) {
                (u16::MIN as i128, u16::MAX as i128)
            } else if Rc::ptr_eq(&typ, &types.int) {
                (i32::MIN as i128, i32::MAX as i128)
            } else if Rc::ptr_eq(&typ, &types.uint) {
                (u32::MIN as i128, u32::MAX as i128)
            } else if Rc::ptr_eq(&typ, &types.long) {
                (i64::MIN as i128, i64::MAX as i128)
            } else if Rc::ptr_eq(&typ, &types.ulong) {
                (u64::MIN as i128, u64::MAX as i128)
            } else {
                return Err(AnalysisError::BadIntegerLiteral(literal.num));
            };

            if literal.num < min || literal.num > max {
                return Err(AnalysisError::BadIntegerLiteral(literal.num));
            }

            Ok(sst::Expression {
                typ,
                kind: sst::ExprKind::Literal(sst::Literal::Integer(literal.num)),
            })
        }

        ast::LiteralExpr::String(str) => {
            let mut frame = scope.frame.borrow_mut();
            let sc = frame.ctx.add_string(str.clone());
            Ok(sst::Expression {
                typ: frame.ctx.types.voidptr.clone(),
                kind: sst::ExprKind::Literal(sst::Literal::String(sc)),
            })
        }

        ast::LiteralExpr::Bool(b) => {
            let frame = scope.frame.borrow();
            Ok(sst::Expression {
                typ: frame.ctx.types.bool.clone(),
                kind: sst::ExprKind::Literal(sst::Literal::Bool(*b)),
            })
        }
    }
}

fn analyze_expression(
    scope: Rc<Scope>,
    expr: &ast::Expression,
    inferred: Option<Rc<sst::Type>>,
) -> Result<sst::Expression> {
    let expr = match expr {
        ast::Expression::Literal(literal) => {
            analyze_literal(scope.clone(), literal, inferred.clone())?
        }

        ast::Expression::FuncCall(ident, params) => {
            let sig = scope.get_func_sig(ident)?;

            let len = sig.params.fields.len();
            if len != params.len() {
                return Err(AnalysisError::BadParamCount(len, params.len()));
            }

            let mut exprs = Vec::<sst::Expression>::new();
            exprs.reserve(len);
            for i in 0..len {
                exprs.push(analyze_expression(
                    scope.clone(),
                    &params[i],
                    Some(sig.params.fields[i].typ.clone()),
                )?);
            }

            scope.props.borrow_mut().is_leaf = false;

            sst::Expression {
                typ: sig.ret.clone(),
                kind: sst::ExprKind::FuncCall(sig, exprs),
            }
        }

        ast::Expression::Assignment(ident, expr) => {
            let var = scope.lookup(ident.clone())?;
            let expr = analyze_expression(scope, expr, Some(var.typ.clone()))?;
            sst::Expression {
                typ: var.typ.clone(),
                kind: sst::ExprKind::Assignment(var, Box::new(expr)),
            }
        }

        ast::Expression::Uninitialized(maybe_type) => {
            if let Some(typ) = maybe_type {
                sst::Expression {
                    typ: scope.get_type(typ)?,
                    kind: sst::ExprKind::Uninitialized,
                }
            } else if let Some(inferred) = &inferred {
                sst::Expression {
                    typ: inferred.clone(),
                    kind: sst::ExprKind::Uninitialized,
                }
            } else {
                return Err(AnalysisError::InconclusiveInference);
            }
        }

        ast::Expression::Variable(name) => {
            let var = scope.lookup(name.clone())?;
            sst::Expression {
                typ: var.typ.clone(),
                kind: sst::ExprKind::Variable(var.clone()),
            }
        }

        ast::Expression::Group(expr) => analyze_expression(scope, expr, inferred.clone())?,

        ast::Expression::BinOp(lhs, op, rhs) => {
            let (sst_op, is_bool, flip) = match op {
                ast::BinOp::Add => (sst::BinOp::Add, false, false),
                ast::BinOp::Sub => (sst::BinOp::Sub, false, false),
                ast::BinOp::Mul => (sst::BinOp::Mul, false, false),
                ast::BinOp::Div => (sst::BinOp::Div, false, false),
                ast::BinOp::Eq => (sst::BinOp::Eq, true, false),
                ast::BinOp::Neq => (sst::BinOp::Neq, true, false),
                ast::BinOp::Lt => (sst::BinOp::Lt, true, false),
                ast::BinOp::Leq => (sst::BinOp::Leq, true, false),
                ast::BinOp::Gt => (sst::BinOp::Lt, true, true),
                ast::BinOp::Geq => (sst::BinOp::Leq, true, true),
            };

            let (subexpr_type, expr_type) = match is_bool {
                false => (inferred.clone(), inferred.clone()),
                true => (None, Some(scope.frame.borrow().ctx.types.bool.clone())),
            };

            let mut sst_lhs = Box::new(analyze_expression(
                scope.clone(), lhs, subexpr_type)?);
            let mut sst_rhs = Box::new(analyze_expression(
                scope.clone(), rhs, Some(sst_lhs.typ.clone()))?);

            if flip {
                let tmp = sst_lhs;
                sst_lhs = sst_rhs;
                sst_rhs = tmp;
            }

            sst::Expression{
                typ: expr_type.unwrap_or(sst_lhs.typ.clone()),
                kind: sst::ExprKind::BinOp(sst_lhs, sst_op, sst_rhs),
            }
        }
    };

    if let Some(inferred) = &inferred {
        if !Rc::ptr_eq(inferred, &expr.typ) {
            return Err(AnalysisError::TypeConflict(inferred.clone(), expr.typ));
        }
    }

    Ok(expr)
}

fn analyze_statement(scope: Rc<Scope>, stmt: &ast::Statement) -> Result<sst::Statement> {
    match stmt {
        ast::Statement::If(cond, body, else_body) => {
            let bool = scope.frame.borrow().ctx.types.bool.clone();
            let sst_cond = Box::new(analyze_expression(scope.clone(), cond, Some(bool))?);
            let sst_body = Box::new(analyze_statement(scope.clone(), body)?);
            let sst_else_body = match else_body {
                Some(else_body) => Box::new(analyze_statement(scope, else_body)?),
                None => Box::new(sst::Statement::Empty),
            };

            Ok(sst::Statement::If(sst_cond, sst_body, sst_else_body))
        }

        ast::Statement::Return(expr) => {
            let void = scope.frame.borrow().ctx.types.void.clone();
            let ret = scope.frame.borrow().ret.clone();
            let sst_expr = match expr {
                Some(expr) => Some(Box::new(analyze_expression(
                    scope.clone(),
                    expr,
                    Some(ret.clone()),
                )?)),
                None => None,
            };

            if sst_expr.is_none() && !Rc::ptr_eq(&ret, &void) {
                return Err(AnalysisError::TypeConflict(ret, void));
            }

            scope.props.borrow_mut().always_returns = true;
            Ok(sst::Statement::Return(sst_expr))
        }

        ast::Statement::TypeAlias(ident, spec) => {
            let typ = scope.get_type(spec)?;
            scope.declare_type_alias(ident.clone(), typ)?;
            Ok(sst::Statement::Empty)
        }

        ast::Statement::DebugPrint(expr) => {
            let sst_expr = analyze_expression(scope, expr, None)?;
            eprintln!("DEBUG: Expression has type '{}'", sst_expr.typ.name);
            Ok(sst::Statement::Empty)
        }

        ast::Statement::VarDecl(ident, expr) => {
            let sst_expr = Box::new(analyze_expression(scope.clone(), expr, None)?);
            let var = scope.declare(ident.clone(), sst_expr.typ.clone())?;
            Ok(sst::Statement::VarDecl(var, sst_expr))
        }

        ast::Statement::Block(stmts) => {
            let subscope = Scope::from_parent(scope.clone());
            let sst_stmts = analyze_block(subscope.clone(), stmts)?;

            if !subscope.props.borrow().is_leaf {
                scope.props.borrow_mut().is_leaf = false;
            }

            // TODO: This should really consider both branches of an if
            if !subscope.props.borrow().always_returns {
                scope.props.borrow_mut().always_returns = false;
            }

            Ok(sst::Statement::Block(sst_stmts))
        }

        ast::Statement::Expression(expr) => {
            let sst_expr = analyze_expression(scope, expr, None)?;
            Ok(sst::Statement::Expression(Box::new(sst_expr)))
        }
    }
}

fn analyze_block(scope: Rc<Scope>, block: &ast::Block) -> Result<Vec<sst::Statement>> {
    let mut sst_stmts = Vec::<sst::Statement>::new();
    for stmt in block {
        // Eliminate obviously dead code
        if scope.props.borrow().always_returns {
            return Ok(sst_stmts);
        }

        let sst_stmt = analyze_statement(scope.clone(), stmt)?;
        match sst_stmt {
            sst::Statement::Empty => (),
            _ => sst_stmts.push(sst_stmt),
        }
    }

    Ok(sst_stmts)
}

fn analyze_func_decl(ctx: &mut Context, fd: &ast::FuncDecl) -> Result<Rc<sst::Function>> {
    let name = ident_to_name(&fd.signature.ident);
    if ctx.decls.contains_key(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    let params = analyze_field_decls(ctx, &fd.signature.params, None)?;
    let return_type = get_type(ctx, &fd.signature.ret, None)?;
    let voidptr_type = ctx.types.voidptr.clone();

    let frame = StackFrame::new(ctx, return_type.clone());
    let root_scope = Scope::new(frame.clone());
    let underscore = frame.borrow().ctx.underscore.clone();

    // First put the return value on the stack
    let return_var = root_scope.declare(underscore.clone(), return_type.clone())?;

    // Then, all function parameters, in forward order
    for param in &params.fields {
        root_scope.declare(param.name.clone(), param.typ.clone())?;
    }

    // And after that, the return address
    let return_addr = root_scope.declare(underscore, voidptr_type)?;

    let body_scope = Scope::from_parent(root_scope);
    let stmts = analyze_block(body_scope.clone(), &fd.body)?;

    let returns_void = match return_type.kind {
        sst::TypeKind::Primitive(sst::Primitive::Void) => true,
        _ => false,
    };

    let props = body_scope.props.borrow();
    let func = Rc::new(sst::Function {
        signature: Rc::new(sst::FuncSignature {
            name: name.clone(),
            params,
            ret: return_type,
        }),
        return_addr,
        return_var,
        body: stmts,
        stack_size: frame.borrow().size,
        always_returns: props.always_returns,
        is_leaf: props.is_leaf,
    });
    drop(props);

    if !returns_void && !func.always_returns {
        return Err(AnalysisError::NonVoidFunctionMustReturn);
    }

    ctx.decls
        .insert(name, sst::Declaration::Function(func.clone()));
    Ok(func)
}

fn analyze_extern_func_decl(
    ctx: &mut Context,
    efd: &ast::FuncSignature,
) -> Result<Rc<sst::FuncSignature>> {
    let name = ident_to_name(&efd.ident);
    if ctx.decls.contains_key(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    let params = analyze_field_decls(ctx, &efd.params, None)?;
    let ret = get_type(ctx, &efd.ret, None)?;

    let extern_func = Rc::new(sst::FuncSignature {
        name: name.clone(),
        params,
        ret,
    });

    ctx.decls
        .insert(name, sst::Declaration::ExternFunc(extern_func.clone()));
    Ok(extern_func)
}

pub fn program(prog: &ast::Program) -> Result<sst::Program> {
    let primitive = |name: &str, size: usize, kind: sst::Primitive| {
        Rc::new(sst::Type {
            name: Rc::new(name.into()),
            size,
            align: size,
            kind: sst::TypeKind::Primitive(kind),
        })
    };

    let void = primitive("void", 0, sst::Primitive::Void);
    let types = Types {
        void: void.clone(),
        byte: primitive("byte", 1, sst::Primitive::UInt),
        bool: primitive("bool", 1, sst::Primitive::UInt),
        short: primitive("short", 2, sst::Primitive::Int),
        ushort: primitive("ushort", 2, sst::Primitive::UInt),
        int: primitive("int", 4, sst::Primitive::Int),
        uint: primitive("uint", 4, sst::Primitive::UInt),
        long: primitive("long", 8, sst::Primitive::Int),
        ulong: primitive("ulong", 8, sst::Primitive::UInt),
        float: primitive("float", 4, sst::Primitive::Float),
        double: primitive("double", 8, sst::Primitive::Float),
        voidptr: Rc::new(sst::Type {
            name: Rc::new("ptr[void]".to_owned()),
            size: 8,
            align: 8,
            kind: sst::TypeKind::Pointer(void),
        }),
    };

    let mut ctx = Context::new(types);

    let mut functions = Vec::<Rc<sst::Function>>::new();
    for decl in prog {
        let ctx = &mut ctx;
        match decl {
            ast::Declaration::Struct(sd) => {
                analyze_struct_decl(ctx, sd)?;
            }

            ast::Declaration::Func(fd) => match analyze_func_decl(ctx, fd) {
                Ok(decl) => functions.push(decl),
                Err(err) => {
                    let name = ident_to_name(&fd.signature.ident);
                    let err = Box::new(err);
                    return Err(AnalysisError::FunctionCtx(name, err));
                }
            },

            ast::Declaration::ExternFunc(efd) => {
                analyze_extern_func_decl(ctx, efd)?;
            }
        }
    }

    Ok(sst::Program {
        functions,
        strings: ctx.string_constants,
    })
}
