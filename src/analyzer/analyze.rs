use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt::{self, Display};
use std::rc::Rc;

use super::context::{Context, Types};
use super::sst;
use crate::parser::ast;

#[derive(Debug)]
pub enum AnalysisError {
    UndeclaredVariable(Rc<String>),
    UndeclaredType(Rc<String>),
    UndeclaredFunction(Rc<String>),
    UndeclaredMember(Rc<String>),
    MultipleDefinitions(Rc<String>),
    TypeConflict(Rc<sst::Type>, Rc<sst::Type>),
    InconclusiveInference,
    BadParamCount(usize, usize),
    BadIntegerLiteral(i128),
    BadTypeParameters,
    NonVoidFunctionMustReturn,
    BadCast(Rc<sst::Type>, Rc<sst::Type>),
    ExpectedStruct(Rc<sst::Type>),
    ExpectedPointer(Rc<sst::Type>),
    BadStructInitializerName(Rc<String>, Rc<String>),
    ExpectedLValue,

    InternalError(String),

    FunctionCtx(Rc<String>, Box<AnalysisError>),

    // Unimplemented is for code that's a work in progress.
    // Most of the time, nothing which uses Unimplemented will be committed,
    // so it should always be allowed to be unused.
    #[allow(dead_code)]
    Unimplemented,
}

impl Error for AnalysisError {}

impl Display for AnalysisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AnalysisError::*;
        match self {
            UndeclaredVariable(name) => write!(f, "Undeclared variable: {name}"),
            UndeclaredType(name) => write!(f, "Undeclared type: {name}"),
            UndeclaredFunction(name) => write!(f, "Undeclared function: {name}"),
            UndeclaredMember(name) => write!(f, "Undeclared struct member: {name}"),
            MultipleDefinitions(name) => write!(f, "Multiple definitions of {name}"),
            TypeConflict(expected, actual) => {
                write!(f, "Expected type {}, got {}", expected.name, actual.name)
            }
            InconclusiveInference => write!(f, "Inconclusive type inference"),
            BadParamCount(expected, actual) => {
                write!(f, "Expected {expected} params, got {actual}")
            }
            BadIntegerLiteral(num) => {
                write!(f, "Integer literal {num} inappropriate in this context")
            }
            BadTypeParameters => write!(f, "Bad type parameters"),
            NonVoidFunctionMustReturn => write!(f, "Non-void function must return a value"),
            BadCast(from, to) => write!(f, "Illegal cast from {} to {}", from.name, to.name),
            ExpectedStruct(got) => write!(f, "Expecetd struct, got non-struct {}", got.name),
            ExpectedPointer(got) => write!(f, "Expecetd pointer, got non-pointer {}", got.name),
            BadStructInitializerName(expected, got) => {
                write!(f, "Expected initializer for {expected} here, got {got}")
            }
            ExpectedLValue => write!(f, "Expected lvalue"),

            InternalError(msg) => write!(f, "Internal error: {msg}"),

            FunctionCtx(name, err) => write!(f, "In function {name}: {err}"),

            Unimplemented => write!(f, "Feature not implemented"),
        }
    }
}

type Result<T> = std::result::Result<T, AnalysisError>;

struct ScopeProps {
    always_returns: Option<bool>,
    is_leaf: bool,
}

impl ScopeProps {
    fn new() -> Self {
        Self {
            always_returns: None,
            is_leaf: true,
        }
    }
}

struct Scope {
    frame: Rc<RefCell<StackFrame>>,
    parent: Option<Rc<Scope>>,
    vars: RefCell<HashMap<Rc<String>, Rc<sst::LocalVar>>>,
    types: RefCell<HashMap<Rc<String>, Rc<sst::Type>>>,
    offset: RefCell<usize>,
    props: RefCell<ScopeProps>,
}

impl Scope {
    fn new(frame: Rc<RefCell<StackFrame>>) -> Rc<Self> {
        Rc::new(Self {
            frame,
            parent: None,
            vars: RefCell::new(HashMap::new()),
            types: RefCell::new(HashMap::new()),
            offset: RefCell::new(0),
            props: RefCell::new(ScopeProps::new()),
        })
    }

    fn from_parent(parent: Rc<Scope>) -> Rc<Self> {
        let offset = *parent.offset.borrow();
        Rc::new(Self {
            frame: parent.frame.clone(),
            parent: Some(parent),
            vars: RefCell::new(HashMap::new()),
            types: RefCell::new(HashMap::new()),
            offset: RefCell::new(offset),
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
        get_type(&self.frame.borrow_mut().ctx, spec, Some(self))
    }

    fn get_func_sig_from_name(&self, name: &Rc<String>) -> Result<Rc<sst::FuncSignature>> {
        let frame = self.frame.borrow();
        let Some(decl) = frame.ctx.get_decl(&name) else {
            return Err(AnalysisError::UndeclaredFunction(name.clone()));
        };

        match decl {
            sst::Declaration::Function(func) => Ok(func.signature.clone()),
            sst::Declaration::ExternFunc(sig) => Ok(sig.clone()),
            _ => Err(AnalysisError::UndeclaredFunction(name.clone())),
        }
    }

    fn get_func_sig(&self, name: &ast::FuncName) -> Result<Rc<sst::FuncSignature>> {
        self.get_func_sig_from_name(&func_to_name(name))
    }
}

struct StackFrame {
    ctx: Rc<Context>,
    size: usize,
    ret: Rc<sst::Type>,
}

impl StackFrame {
    fn new(ctx: Rc<Context>, ret: Rc<sst::Type>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self { ctx, size: 0, ret }))
    }
}

fn write_spec_to_name(spec: &ast::TypeSpec, out: &mut String) {
    out.push_str(&spec.ident);
    if !spec.params.is_empty() {
        out.push('[');
        let mut first = true;
        for ast::TypeParam::Type(part) in &spec.params {
            if !first {
                out.push(',');
            }
            first = false;

            write_spec_to_name(part, out);
        }
        out.push(']');
    }
}

fn func_to_name(name: &ast::FuncName) -> Rc<String> {
    if name.typ.is_none() {
        return name.ident.clone();
    }

    let mut s = String::new();
    if let Some(spec) = &name.typ {
        write_spec_to_name(spec, &mut s);
        s.push_str("::");
    }

    s.push_str(&name.ident);
    Rc::new(s)
}

fn get_type(
    ctx: &Rc<Context>,
    spec: &ast::TypeSpec,
    scope: Option<&Scope>,
) -> Result<Rc<sst::Type>> {
    let ident = &spec.ident;

    if ident.as_str() == "ptr" {
        if spec.params.len() != 1 {
            return Err(AnalysisError::BadTypeParameters);
        }

        let ast::TypeParam::Type(typ) = &spec.params[0];
        let typ = get_type(ctx, typ, scope)?;
        return Ok(make_pointer_to(ctx, &typ));
    }

    if spec.params.is_empty() {
        if let Some(typ) = scope.and_then(|scope| scope.get_type_alias(&ident)) {
            return Ok(typ);
        }

        if let Some(sst::Declaration::Type(typ)) = ctx.get_decl(&ident) {
            return Ok(typ.clone());
        }

        eprintln!("during get_type {:?}: undeclared type {}", spec, ident);
        return Err(AnalysisError::UndeclaredType(ident.clone()));
    }

    if let Some(st) = ctx.get_struct_template(&ident) {
        let st = st.clone();
        if spec.params.len() != st.type_params.len() {
            return Err(AnalysisError::BadParamCount(
                st.type_params.len(),
                spec.params.len(),
            ));
        }

        let mut tname = st.name.as_ref().clone();
        tname += "[";

        let mut types = HashMap::<Rc<String>, Rc<sst::Type>>::new();
        for (i, param) in spec.params.iter().enumerate() {
            let name = &st.type_params[i];
            let ast::TypeParam::Type(subspec) = param;
            let typ = get_type(ctx, subspec, scope)?;
            if i != 0 {
                tname += ",";
            }
            tname += &typ.name;

            types.insert(name.clone(), typ);
        }

        tname += "]";
        let tname = Rc::new(tname);

        if let Some(sst::Declaration::Type(typ)) = ctx.get_decl(&tname) {
            return Ok(typ.clone());
        }

        let void = ctx.types.void.clone();
        let struct_scope = Scope {
            frame: StackFrame::new(ctx.clone(), void),
            parent: None,
            vars: RefCell::new(HashMap::new()),
            types: RefCell::new(types),
            offset: RefCell::new(0),
            props: RefCell::new(ScopeProps::new()),
        };

        let info = analyze_field_decls(
            &struct_scope.frame.borrow_mut().ctx,
            &st.fields,
            Some(&struct_scope),
        )?;
        let fields = info.fields;

        let typ = Rc::new(sst::Type {
            name: tname.clone(),
            size: info.size,
            align: info.align,
            kind: sst::TypeKind::Struct(Rc::new(sst::Struct {
                name: tname.clone(),
                fields,
            })),
        });
        ctx.add_decl(tname, sst::Declaration::Type(typ.clone()));
        return Ok(typ);
    }

    Err(AnalysisError::UndeclaredType(ident.clone()))
}

fn make_pointer_to(ctx: &Rc<Context>, typ: &Rc<sst::Type>) -> Rc<sst::Type> {
    let name = Rc::new(format!("ptr[{}]", typ.name));
    if let Some(sst::Declaration::Type(typ)) = ctx.get_decl(&name) {
        return typ.clone();
    }

    let ptr = Rc::new(sst::Type {
        name: name.clone(),
        size: 8,
        align: 8,
        kind: sst::TypeKind::Pointer(typ.clone()),
    });
    ctx.add_decl(name, sst::Declaration::Type(ptr.clone()));
    ptr
}

fn make_span_of(ctx: &Rc<Context>, typ: &Rc<sst::Type>) -> Rc<sst::Type> {
    let name = Rc::new(format!("span[{}]", typ.name));
    if let Some(sst::Declaration::Type(typ)) = ctx.get_decl(&name) {
        return typ.clone();
    }

    let ptr_type = make_pointer_to(ctx, typ);

    let typ = Rc::new(sst::Type {
        name: name.clone(),
        size: 16,
        align: 8,
        kind: sst::TypeKind::Struct(Rc::new(sst::Struct {
            name: name.clone(),
            fields: vec![
                sst::FieldDecl {
                    name: Rc::new("ptr".into()),
                    typ: ptr_type,
                    offset: 0,
                },
                sst::FieldDecl {
                    name: Rc::new("len".into()),
                    typ: ctx.types.ulong.clone(),
                    offset: 8,
                },
            ],
        })),
    });

    ctx.add_decl(name, sst::Declaration::Type(typ.clone()));
    typ
}

fn analyze_field_decls(
    ctx: &Rc<Context>,
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

fn analyze_struct_decl(ctx: &Rc<Context>, sd: &ast::StructDecl) -> Result<()> {
    let name = sd.name.clone();
    if ctx.has_decl(&name) || ctx.has_struct_template(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    // Templates must be dealt with later
    if !sd.type_params.is_empty() {
        ctx.add_struct_template(name, sd.clone());
        return Ok(());
    }

    let info = analyze_field_decls(ctx, &sd.fields, None)?;
    let fields = info.fields;

    let typ = Rc::new(sst::Type {
        name: name.clone(),
        size: info.size,
        align: info.align,
        kind: sst::TypeKind::Struct(Rc::new(sst::Struct {
            name: name.clone(),
            fields,
        })),
    });

    ctx.add_decl(name, sst::Declaration::Type(typ));
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
    scope: &Rc<Scope>,
    literal: &ast::LiteralExpr,
    inferred: Option<Rc<sst::Type>>,
) -> Result<sst::Expression> {
    match literal {
        ast::LiteralExpr::Struct(literal) => {
            let typ = scope.get_type(&literal.typ)?;
            let sst::TypeKind::Struct(s) = &typ.kind else {
                return Err(AnalysisError::ExpectedStruct(typ));
            };

            let count = s.fields.len();
            if count != literal.initializers.len() {
                return Err(AnalysisError::BadParamCount(
                    count,
                    literal.initializers.len(),
                ));
            }

            let mut exprs = Vec::<sst::Expression>::with_capacity(count);
            for i in 0..count {
                let decl = &s.fields[i];
                let initializer = &literal.initializers[i];
                if initializer.name.as_str() != "_"
                    && initializer.name.as_str() != decl.name.as_str()
                {
                    return Err(AnalysisError::BadStructInitializerName(
                        decl.name.clone(),
                        initializer.name.clone(),
                    ));
                }

                exprs.push(analyze_expression(
                    scope,
                    &initializer.expr,
                    Some(decl.typ.clone()),
                )?);
            }

            Ok(sst::Expression {
                typ: typ.clone(),
                kind: sst::ExprKind::Literal(sst::Literal::Struct(s.clone(), exprs)),
            })
        }

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
            let frame = scope.frame.borrow_mut();
            let sc = frame.ctx.add_string(&str);
            Ok(sst::Expression {
                typ: make_span_of(&frame.ctx, &frame.ctx.types.byte),
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

fn check_cast(from: &Rc<sst::Type>, to: &Rc<sst::Type>) -> Result<()> {
    let is_integral = |x: &sst::TypeKind| {
        matches!(
            x,
            sst::TypeKind::Primitive(sst::Primitive::Int)
                | sst::TypeKind::Primitive(sst::Primitive::UInt)
        )
    };

    let is_pointer = |x: &sst::TypeKind| matches!(x, sst::TypeKind::Pointer(..));

    let is_ulong = |x: &sst::Type| {
        x.size == 8 && matches!(x.kind, sst::TypeKind::Primitive(sst::Primitive::UInt))
    };

    if is_integral(&from.kind) && is_integral(&to.kind) {
        return Ok(());
    }

    if is_pointer(&from.kind) && is_pointer(&to.kind) {
        return Ok(());
    }

    if is_pointer(&from.kind) && is_ulong(&to) {
        return Ok(());
    }

    if is_ulong(&from) && is_pointer(&to.kind) {
        return Ok(());
    }

    Err(AnalysisError::BadCast(from.clone(), to.clone()))
}

fn analyze_func_call(
    scope: &Rc<Scope>,
    name: &ast::FuncName,
    params: &[ast::Expression],
) -> Result<sst::Expression> {
    let maybe_sig = scope.get_func_sig(name);

    // A function might be a cast,
    // since casts and function calls can't be properly distinguished by the parser
    if let Err(err) = maybe_sig {
        if params.len() != 1 {
            return Err(err);
        }

        if name.typ.is_some() {
            return Err(err);
        }

        let spec = ast::TypeSpec {
            ident: name.ident.clone(),
            params: Vec::new(),
        };

        let Ok(typ) = scope.get_type(&spec) else {
            return Err(err);
        };

        let sst_expr = analyze_expression_non_typechecked(scope, &params[0], Some(typ.clone()))?;

        if Rc::ptr_eq(&sst_expr.typ, &typ) {
            return Ok(sst_expr);
        }

        check_cast(&sst_expr.typ, &typ)?;
        return Ok(sst::Expression {
            typ,
            kind: sst::ExprKind::Cast(Box::new(sst_expr)),
        });
    }

    let sig = maybe_sig?;

    let len = sig.params.fields.len();
    if len != params.len() {
        return Err(AnalysisError::BadParamCount(len, params.len()));
    }

    let mut exprs = Vec::<sst::Expression>::with_capacity(len);
    for (i, field) in sig.params.fields.iter().enumerate() {
        exprs.push(analyze_expression(
            &scope,
            &params[i],
            Some(field.typ.clone()),
        )?);
    }

    scope.props.borrow_mut().is_leaf = false;

    Ok(sst::Expression {
        typ: sig.ret.clone(),
        kind: sst::ExprKind::FuncCall(sig, exprs),
    })
}

fn analyze_expression_non_typechecked(
    scope: &Rc<Scope>,
    expr: &ast::Expression,
    inferred: Option<Rc<sst::Type>>,
) -> Result<sst::Expression> {
    let expr = match expr {
        ast::Expression::Literal(literal) => analyze_literal(scope, literal, inferred.clone())?,

        ast::Expression::FuncCall(ident, params) => analyze_func_call(scope, ident, params)?,

        ast::Expression::Cast(spec, expr) => {
            let typ = scope.get_type(spec)?;
            let sst_expr = analyze_expression_non_typechecked(scope, expr, Some(typ.clone()))?;
            if Rc::ptr_eq(&sst_expr.typ, &typ) {
                sst_expr
            } else {
                check_cast(&sst_expr.typ, &typ)?;
                sst::Expression {
                    typ,
                    kind: sst::ExprKind::Cast(Box::new(sst_expr)),
                }
            }
        }

        ast::Expression::Assignment(dest, src) => {
            let sst_dest = analyze_expression(scope, dest, None)?;
            let dest_typ = sst_dest.typ;
            let sst::ExprKind::LValue(lvalue) = sst_dest.kind else {
                return Err(AnalysisError::ExpectedLValue);
            };

            let sst_dest = sst::Expression::<sst::LValue> {
                typ: dest_typ,
                kind: lvalue,
            };

            let sst_src = analyze_expression(scope, src, Some(sst_dest.typ.clone()))?;
            sst::Expression {
                typ: sst_dest.typ.clone(),
                kind: sst::ExprKind::Assignment(Box::new(sst_dest), Box::new(sst_src)),
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
                kind: sst::ExprKind::LValue(sst::LValue::Variable(var.clone())),
            }
        }

        ast::Expression::Group(expr) => {
            analyze_expression_non_typechecked(scope, expr, inferred.clone())?
        }

        ast::Expression::BinOp(lhs, op, rhs) => {
            let (sst_op, is_bool, flip) = match op {
                ast::BinOp::Mul => (sst::BinOp::Mul, false, false),
                ast::BinOp::Div => (sst::BinOp::Div, false, false),
                ast::BinOp::Mod => (sst::BinOp::Mod, false, false),
                ast::BinOp::Add => (sst::BinOp::Add, false, false),
                ast::BinOp::Sub => (sst::BinOp::Sub, false, false),
                ast::BinOp::Eq => (sst::BinOp::Eq, true, false),
                ast::BinOp::Neq => (sst::BinOp::Neq, true, false),
                ast::BinOp::Lt => (sst::BinOp::Lt, true, false),
                ast::BinOp::Leq => (sst::BinOp::Leq, true, false),
                ast::BinOp::Gt => (sst::BinOp::Lt, true, true),
                ast::BinOp::Geq => (sst::BinOp::Leq, true, true),
            };

            let (subexpr_type, expr_type) = match is_bool {
                false => (inferred.clone(), None),
                true => (None, Some(scope.frame.borrow().ctx.types.bool.clone())),
            };

            let mut sst_lhs = Box::new(analyze_expression_non_typechecked(
                scope,
                lhs,
                subexpr_type,
            )?);

            let mut sst_rhs = Box::new(analyze_expression(scope, rhs, Some(sst_lhs.typ.clone()))?);

            if flip {
                std::mem::swap(&mut sst_lhs, &mut sst_rhs);
            }

            sst::Expression {
                typ: expr_type.unwrap_or(sst_lhs.typ.clone()),
                kind: sst::ExprKind::BinOp(sst_lhs, sst_op, sst_rhs),
            }
        }

        ast::Expression::Reference(expr) => {
            let sst_expr = analyze_expression(scope, expr, None)?;

            sst::Expression {
                typ: make_pointer_to(&scope.frame.borrow_mut().ctx, &sst_expr.typ),
                kind: sst::ExprKind::Reference(Box::new(sst_expr)),
            }
        }

        ast::Expression::Dereference(expr) => {
            let sst_expr = analyze_expression(scope, expr, None)?;
            let typ = match &sst_expr.typ.kind {
                sst::TypeKind::Pointer(typ) => typ.clone(),
                _ => return Err(AnalysisError::ExpectedPointer(sst_expr.typ.clone())),
            };
            sst::Expression {
                typ,
                kind: sst::ExprKind::LValue(sst::LValue::Dereference(Box::new(sst_expr))),
            }
        }

        ast::Expression::MemberAccess(expr, ident) => {
            let sst_expr = analyze_expression(scope, expr, None)?;
            let sst::TypeKind::Struct(s) = &sst_expr.typ.kind else {
                return Err(AnalysisError::ExpectedStruct(sst_expr.typ.clone()));
            };

            let Some(field) = s.field(ident.as_str()) else {
                return Err(AnalysisError::UndeclaredMember(ident.clone()));
            };

            match &sst_expr.kind {
                // If the subject is already a dereference,
                // generate a DerefAccess instead of a Dereference + MemberAccess.
                sst::ExprKind::LValue(sst::LValue::Dereference(subexpr)) => sst::Expression {
                    typ: field.typ.clone(),
                    kind: sst::ExprKind::LValue(sst::LValue::DerefAccess(subexpr.clone(), field)),
                },

                // If it's a DerefAccess, apply the appropriate offset.
                sst::ExprKind::LValue(sst::LValue::DerefAccess(expr, base)) => sst::Expression {
                    typ: field.typ.clone(),
                    kind: sst::ExprKind::LValue(sst::LValue::DerefAccess(
                        expr.clone(),
                        sst::FieldDecl {
                            name: Rc::new(format!("{}.{}", base.name, field.name)),
                            typ: field.typ.clone(),
                            offset: base.offset + field.offset,
                        },
                    )),
                },

                // If it's a MemberAccess, apply the appropriate offset.
                sst::ExprKind::LValue(sst::LValue::MemberAccess(expr, base)) => sst::Expression {
                    typ: field.typ.clone(),
                    kind: sst::ExprKind::LValue(sst::LValue::MemberAccess(
                        expr.clone(),
                        sst::FieldDecl {
                            name: Rc::new(format!("{}.{}", base.name, field.name)),
                            typ: field.typ.clone(),
                            offset: base.offset + field.offset,
                        },
                    )),
                },

                // Otherwise, keep it as it is.
                _ => sst::Expression {
                    typ: field.typ.clone(),
                    kind: sst::ExprKind::LValue(sst::LValue::MemberAccess(
                        Box::new(sst_expr),
                        field,
                    )),
                },
            }
        }

        ast::Expression::MethodCall(subject, ident, params) => {
            let sst_subject = analyze_expression(scope, subject, None)?;
            let func_name = Rc::new(format!("{}::{}", sst_subject.typ.name, ident));

            // If the subject is already a dereference, don't referenc it again,
            // just use the pointer we already have
            let subject_ptr = match sst_subject.kind {
                sst::ExprKind::LValue(sst::LValue::Dereference(subexpr)) => {
                    subexpr.as_ref().clone()
                }
                _ => sst::Expression {
                    typ: make_pointer_to(&scope.frame.borrow().ctx, &sst_subject.typ),
                    kind: sst::ExprKind::Reference(Box::new(sst_subject)),
                },
            };

            let sig = scope.get_func_sig_from_name(&func_name)?;

            let len = sig.params.fields.len();
            if len != params.len() + 1 {
                return Err(AnalysisError::BadParamCount(len, params.len() + 1));
            }

            let expected_subject_typ = sig.params.fields.first().unwrap().typ.clone();
            if !Rc::ptr_eq(&expected_subject_typ, &subject_ptr.typ) {
                return Err(AnalysisError::TypeConflict(
                    expected_subject_typ,
                    subject_ptr.typ.clone(),
                ));
            }

            let mut exprs = Vec::<sst::Expression>::with_capacity(params.len() + 1);
            exprs.push(subject_ptr);
            for (i, field) in sig.params.fields.iter().skip(1).enumerate() {
                exprs.push(analyze_expression(
                    scope,
                    &params[i],
                    Some(field.typ.clone()),
                )?);
            }

            scope.props.borrow_mut().is_leaf = false;

            sst::Expression {
                typ: sig.ret.clone(),
                kind: sst::ExprKind::FuncCall(sig, exprs),
            }
        }
    };

    Ok(expr)
}

fn analyze_expression(
    scope: &Rc<Scope>,
    expr: &ast::Expression,
    inferred: Option<Rc<sst::Type>>,
) -> Result<sst::Expression> {
    let sst_expr = analyze_expression_non_typechecked(scope, expr, inferred.clone())?;

    if let Some(inferred) = &inferred {
        if !Rc::ptr_eq(inferred, &sst_expr.typ) {
            return Err(AnalysisError::TypeConflict(inferred.clone(), sst_expr.typ));
        }
    }

    Ok(sst_expr)
}

fn analyze_statement(scope: &Rc<Scope>, stmt: &ast::Statement) -> Result<sst::Statement> {
    match stmt {
        ast::Statement::If(cond, body, else_body) => {
            let bool = scope.frame.borrow().ctx.types.bool.clone();
            let sst_cond = Box::new(analyze_expression(scope, cond, Some(bool))?);

            let ar_before = scope.props.borrow().always_returns;

            scope.props.borrow_mut().always_returns = ar_before;
            let sst_body = Box::new(analyze_statement(scope, body)?);
            let ar_a = scope.props.borrow().always_returns;

            scope.props.borrow_mut().always_returns = ar_before;
            let sst_else_body = match else_body {
                Some(else_body) => Box::new(analyze_statement(scope, else_body)?),
                None => Box::new(sst::Statement::Empty),
            };
            let ar_b = scope.props.borrow().always_returns;

            scope.props.borrow_mut().always_returns = match (ar_a, ar_b) {
                // If either side *knows* that it won't always return,
                // we know we won't always return
                (Some(false), ..) | (.., Some(false)) => Some(false),

                // If both sides *know* thatt hey always return,
                // we know we always return
                (Some(true), Some(true)) => Some(true),

                // Anything else is inconclusive
                _ => None,
            };

            Ok(sst::Statement::If(sst_cond, sst_body, sst_else_body))
        }

        ast::Statement::Loop(body) => {
            let sst_body = Box::new(analyze_statement(scope, body)?);
            // If we don't know whether we always return after parsing the body,
            // we *will* always return (or never break),
            // because that means there's no break statement in the body.
            // If we know we won't always return, that's due to a break;
            // after the loop, we go back to not knowing.
            if scope.props.borrow().always_returns.is_none() {
                scope.props.borrow_mut().always_returns = Some(true);
            } else if scope.props.borrow().always_returns == Some(false) {
                scope.props.borrow_mut().always_returns = None;
            }
            Ok(sst::Statement::Loop(sst_body))
        }

        ast::Statement::Return(expr) => {
            let void = scope.frame.borrow().ctx.types.void.clone();
            let ret = scope.frame.borrow().ret.clone();
            let sst_expr = match expr {
                Some(expr) => Some(Box::new(analyze_expression(
                    scope,
                    expr,
                    Some(ret.clone()),
                )?)),
                None => None,
            };

            if sst_expr.is_none() && !Rc::ptr_eq(&ret, &void) {
                return Err(AnalysisError::TypeConflict(ret, void));
            }

            if scope.props.borrow().always_returns.is_none() {
                scope.props.borrow_mut().always_returns = Some(true);
            }
            Ok(sst::Statement::Return(sst_expr))
        }

        ast::Statement::Break => {
            scope.props.borrow_mut().always_returns = Some(false);
            Ok(sst::Statement::Break)
        }

        ast::Statement::TypeAlias(ident, spec) => {
            let typ = scope.get_type(spec)?;
            scope.declare_type_alias(ident.clone(), typ)?;
            Ok(sst::Statement::Empty)
        }

        ast::Statement::DebugPrint(expr) => {
            let sst_expr = analyze_expression(scope, expr, None)?;
            eprintln!(
                "DEBUG: Expression has type '{}', size {}",
                sst_expr.typ.name, sst_expr.typ.size,
            );
            if let sst::ExprKind::LValue(sst::LValue::Variable(var)) = sst_expr.kind {
                eprintln!(" -> Frame offset: {}", var.frame_offset);
            }
            Ok(sst::Statement::Empty)
        }

        ast::Statement::VarDecl(ident, expr) => {
            let sst_expr = Box::new(analyze_expression(scope, expr, None)?);
            let var = scope.declare(ident.clone(), sst_expr.typ.clone())?;
            Ok(sst::Statement::VarDecl(var, sst_expr))
        }

        ast::Statement::Block(stmts) => {
            let subscope = Scope::from_parent(scope.clone());
            let sst_stmts = analyze_block(&subscope, stmts)?;

            if !subscope.props.borrow().is_leaf {
                scope.props.borrow_mut().is_leaf = false;
            }

            if let Some(ar) = subscope.props.borrow().always_returns {
                scope.props.borrow_mut().always_returns = Some(ar);
            }

            Ok(sst::Statement::Block(sst_stmts))
        }

        ast::Statement::Debugger => Ok(sst::Statement::Debugger),

        ast::Statement::Expression(expr) => {
            let sst_expr = analyze_expression(scope, expr, None)?;
            Ok(sst::Statement::Expression(Box::new(sst_expr)))
        }
    }
}

fn analyze_block(scope: &Rc<Scope>, block: &ast::Block) -> Result<Vec<sst::Statement>> {
    let mut sst_stmts = Vec::<sst::Statement>::new();
    for stmt in block {
        // Eliminate obviously dead code
        if scope.props.borrow().always_returns == Some(true) {
            return Ok(sst_stmts);
        }

        let sst_stmt = analyze_statement(scope, stmt)?;
        match sst_stmt {
            sst::Statement::Empty => (),
            _ => sst_stmts.push(sst_stmt),
        }
    }

    Ok(sst_stmts)
}

fn analyze_func_decl(ctx: &Rc<Context>, fd: &ast::FuncDecl) -> Result<Rc<sst::Function>> {
    let name = func_to_name(&fd.signature.name);

    let params = analyze_field_decls(ctx, &fd.signature.params, None)?;
    let return_type = get_type(ctx, &fd.signature.ret, None)?;
    let voidptr_type = ctx.types.voidptr.clone();

    let frame = StackFrame::new(ctx.clone(), return_type.clone());
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
    let stmts = analyze_block(&body_scope, &fd.body)?;

    let returns_void = matches!(
        return_type.kind,
        sst::TypeKind::Primitive(sst::Primitive::Void)
    );

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
        always_returns: props.always_returns == Some(true),
        is_leaf: props.is_leaf,
    });
    drop(props);

    if !returns_void && !func.always_returns {
        return Err(AnalysisError::NonVoidFunctionMustReturn);
    }

    ctx.add_decl(name, sst::Declaration::Function(func.clone()));
    Ok(func)
}

fn analyze_extern_func_decl(
    ctx: &Rc<Context>,
    efd: &ast::FuncSignature,
) -> Result<Rc<sst::FuncSignature>> {
    let name = func_to_name(&efd.name);
    if ctx.has_decl(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    let params = analyze_field_decls(ctx, &efd.params, None)?;
    let ret = get_type(ctx, &efd.ret, None)?;

    let extern_func = Rc::new(sst::FuncSignature {
        name: name.clone(),
        params,
        ret,
    });

    ctx.add_decl(name, sst::Declaration::ExternFunc(extern_func.clone()));
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

    let byte = primitive("byte", 1, sst::Primitive::UInt);
    let void = primitive("void", 0, sst::Primitive::Void);
    let types = Types {
        void: void.clone(),
        byte: byte.clone(),
        bool: primitive("bool", 1, sst::Primitive::UInt),
        short: primitive("short", 2, sst::Primitive::Int),
        ushort: primitive("ushort", 2, sst::Primitive::UInt),
        int: primitive("int", 4, sst::Primitive::Int),
        uint: primitive("uint", 4, sst::Primitive::UInt),
        long: primitive("long", 8, sst::Primitive::Int),
        ulong: primitive("ulong", 8, sst::Primitive::UInt),
        float: primitive("float", 4, sst::Primitive::Float),
        double: primitive("double", 8, sst::Primitive::Float),
        byteptr: Rc::new(sst::Type {
            name: Rc::new("ptr[byte]".to_owned()),
            size: 8,
            align: 8,
            kind: sst::TypeKind::Pointer(byte),
        }),
        voidptr: Rc::new(sst::Type {
            name: Rc::new("ptr[void]".to_owned()),
            size: 8,
            align: 8,
            kind: sst::TypeKind::Pointer(void),
        }),
    };

    let ctx = Rc::new(Context::new(types));

    // Create a span struct
    let span_decl = ast::StructDecl {
        name: Rc::new("span".into()),
        fields: vec![
            ast::FieldDecl {
                name: Rc::new("ptr".into()),
                typ: ast::TypeSpec {
                    ident: Rc::new("ptr".into()),
                    params: vec![ast::TypeParam::Type(Box::new(ast::TypeSpec {
                        ident: Rc::new("T".into()),
                        params: vec![],
                    }))],
                },
            },
            ast::FieldDecl {
                name: Rc::new("len".into()),
                typ: ast::TypeSpec {
                    ident: Rc::new("ulong".into()),
                    params: vec![],
                },
            },
        ],
        type_params: vec![Rc::new("T".into())],
    };
    ctx.add_struct_template(span_decl.name.clone(), span_decl);

    // Analyze all declarations, but no function bodies.
    // We do this first so that function bodies can refer to all other functions
    // and all types etc.
    for decl in prog {
        match decl {
            ast::Declaration::Struct(sd) => {
                analyze_struct_decl(&ctx, sd)?;
            }

            ast::Declaration::Func(fd) => {
                // Analyze only the signature first
                analyze_extern_func_decl(&ctx, &fd.signature)?;
            }

            ast::Declaration::ExternFunc(efd) => {
                analyze_extern_func_decl(&ctx, efd)?;
            }
        }
    }

    // Analyze function bodies.
    let mut functions = Vec::<Rc<sst::Function>>::new();
    for decl in prog {
        match decl {
            ast::Declaration::Func(fd) => match analyze_func_decl(&ctx, fd) {
                Ok(decl) => functions.push(decl),
                Err(err) => {
                    let name = func_to_name(&fd.signature.name);
                    let err = Box::new(err);
                    return Err(AnalysisError::FunctionCtx(name, err));
                }
            },
            _ => (),
        }
    }

    let Some(ctx) = Rc::into_inner(ctx) else {
        return Err(AnalysisError::InternalError(
            "Failed to make ctx mutable".into(),
        ));
    };

    Ok(sst::Program {
        functions,
        strings: ctx.done(),
    })
}
