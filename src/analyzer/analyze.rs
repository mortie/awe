#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use crate::parser::ast;
use super::sst;

use std::rc::Rc;

#[derive(Debug)]
pub enum AnalysisError {
    UndeclaredVariable(Rc<String>),
    UndeclaredType(Rc<String>),
    UndeclaredFunction(Rc<String>),
    MultipleDefinitions(Rc<String>),
    TypeConflict(Rc<sst::Type>, Rc<sst::Type>),
    InconclusiveInference,
    BadParamCount(usize, usize),
    Unimplemented,
}

type Result<T> = std::result::Result<T, AnalysisError>;

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

struct Scope<'a> {
    frame: Rc<RefCell<StackFrame<'a>>>,
    parent: Option<Rc<Scope<'a>>>,
    vars: RefCell<HashMap<Rc<String>, Rc<sst::LocalVar>>>,
    offset: RefCell<usize>,
}

impl<'a> Scope<'a> {
    fn new(frame: Rc<RefCell<StackFrame<'a>>>) -> Rc<Self> {
        Rc::new(Self {
            frame,
            parent: None,
            vars: RefCell::new(HashMap::new()),
            offset: RefCell::new(0),
        })
    }

    fn from_parent(parent: Rc<Scope<'a>>) -> Rc<Self> {
        Rc::new(Self {
            frame: parent.frame.clone(),
            parent: Some(parent),
            vars: RefCell::new(HashMap::new()),
            offset: RefCell::new(0),
        })
    }

    fn lookup(&self, name: Rc<String>) -> Option<Rc<sst::LocalVar>> {
        if let Some(var) = self.vars.borrow().get(&name) {
            return Some(var.clone());
        }

        if let Some(parent) = &self.parent {
            return parent.lookup(name);
        }

        None
    }

    fn declare(
        &self,
        name: Rc<String>,
        typ: Rc<sst::Type>,
    ) -> Result<Rc<sst::LocalVar>> {
        let mut vars = self.vars.borrow_mut();
        if vars.contains_key(&name) {
            return Err(AnalysisError::MultipleDefinitions(name));
        }

        let mut offset = self.offset.borrow_mut();
        while typ.size > 0 && *offset % typ.size != 0 {
            *offset += 1;
        }

        let size = typ.size;
        let var = Rc::new(sst::LocalVar{
            typ,
            frame_offset: *offset,
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

    fn get_type(self: Rc<Self>, spec: &ast::TypeSpec) -> Result<Rc<sst::Type>> {
        // TODO: Once type aliases are implemented,
        // this function will resolve local type aliases
        get_type(self.frame.borrow().ctx, spec)
    }

    fn get_func_sig(
        &self,
        ident: &ast::QualifiedIdent,
    ) -> Result<Rc<sst::FuncSignature>> {
        let name = ident_to_name(ident);
        let Some(decl) = self.frame.borrow().ctx.decls.get(&name) else {
            return Err(AnalysisError::UndeclaredFunction(name));
        };

        match decl {
            sst::Declaration::Function(func) => Ok(func.signature.clone()),
            sst::Declaration::ExternFunc(sig) => Ok(sig.clone()),
            _ => Err(AnalysisError::UndeclaredFunction(name))
        }
    }
}

struct StackFrame<'a> {
    ctx: &'a Context,
    size: usize,
}

impl<'a> StackFrame<'a> {
    fn new(ctx: &'a mut Context) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            ctx,
            size: 0,
        }))
    }
}

struct Context {
    decls: HashMap<Rc<String>, sst::Declaration>,
}

impl Context {
    fn add_primitive(&mut self, name: &str, size: usize, kind: sst::Primitive) {
        let name = Rc::new(name.to_owned());
        self.decls.insert(name.clone(), sst::Declaration::Type(Rc::new(sst::Type{
            name,
            size,
            align: size,
            kind: sst::TypeKind::Primitive(kind),
        })));

    }
}

fn get_type(ctx: &Context, spec: &ast::TypeSpec) -> Result<Rc<sst::Type>> {
    // TODO: template params
    let ident = ident_to_name(&spec.ident);
    let Some(decl) = ctx.decls.get(&ident) else {
        return Err(AnalysisError::UndeclaredType(ident));
    };

    let sst::Declaration::Type(typ) = decl else {
        return Err(AnalysisError::UndeclaredType(ident));
    };

    Ok(typ.clone())
}

fn analyze_field_decls(
    ctx: &Context,
    field_decls: &[ast::FieldDecl],
) -> Result<sst::FieldDecls> {
    let mut names = HashSet::<Rc<String>>::new();
    let mut fields = Vec::<sst::FieldDecl>::new();
    let mut offset: usize = 0;
    let mut biggest_align: usize = 0;
    for decl in field_decls {
        let fname = decl.name.clone();
        let typ = get_type(ctx, &decl.typ)?;

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
        fields.push(sst::FieldDecl{
            name: fname,
            typ,
            offset,
        });
        offset += size;
    }

    while biggest_align > 0 && offset % biggest_align != 0 {
        offset += 1;
    }

    Ok(sst::FieldDecls{
        fields,
        size: offset,
        align: biggest_align,
    })
}

fn analyze_struct_decl(
    ctx: &mut Context,
    sd: &ast::StructDecl,
) -> Result<()> {
    let name = sd.name.clone();
    if ctx.decls.contains_key(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    let info = analyze_field_decls(&ctx, &sd.fields)?;

    let mut fields = HashMap::<Rc<String>, sst::FieldDecl>::new();
    for field in info.fields {
        fields.insert(field.name.clone(), field);
    }

    let typ = Rc::new(sst::Type{
        name: name.clone(),
        size: info.size,
        align: info.align,
        kind: sst::TypeKind::Struct(Rc::new(sst::Struct{
            name: name.clone(),
            fields,
            methods: HashMap::new(),
        })),
    });

    ctx.decls.insert(name, sst::Declaration::Type(typ));
    Ok(())
}

fn analyze_expression(
    scope: Rc<Scope>,
    expr: &ast::Expression,
    inferred: Option<Rc<sst::Type>>,
) -> Result<sst::Expression> {
    let expr = match expr {
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
                    scope.clone(), &params[i],
                    Some(sig.params.fields[i].typ.clone()))?);
            }

            sst::Expression{
                typ: sig.ret.clone(),
                kind: sst::ExprKind::FuncCall(sig, exprs),
            }
        }

        ast::Expression::Assignment(_ident, _expr) => {
            return Err(AnalysisError::Unimplemented)
        }

        ast::Expression::Uninitialized(maybe_type) => {
            if let Some(typ) = maybe_type {
                sst::Expression{
                    typ: scope.get_type(typ)?,
                    kind: sst::ExprKind::Uninitialized,
                }
            } else if let Some(inferred) = &inferred {
                sst::Expression{
                    typ: inferred.clone(),
                    kind: sst::ExprKind::Uninitialized,
                }
            } else {
                return Err(AnalysisError::InconclusiveInference)
            }
        }

        ast::Expression::Variable(name) => {
            let Some(var) = scope.lookup(name.clone()) else {
                return Err(AnalysisError::UndeclaredVariable(name.clone()));
            };

            sst::Expression{
                typ: var.typ.clone(),
                kind: sst::ExprKind::Variable(var.clone()),
            }
        }

        ast::Expression::Group(expr) => {
            analyze_expression(scope, expr, inferred.clone())?
        }
    };

    if let Some(inferred) = &inferred {
        if !Rc::ptr_eq(inferred, &expr.typ) {
            return Err(AnalysisError::TypeConflict(inferred.clone(), expr.typ));
        }
    }

    Ok(expr)
}

fn analyze_statement(
    scope: Rc<Scope>,
    stmt: &ast::Statement,
) -> Result<sst::Statement> {
    match stmt {
        ast::Statement::Expression(expr) => {
            let sst_expr = analyze_expression(scope, expr, None)?;
            Ok(sst::Statement::Expression(Box::new(sst_expr)))
        }

        ast::Statement::VarDecl(ident, expr) => {
            let sst_expr = Box::new(analyze_expression(scope.clone(), expr, None)?);
            let var = scope.declare(ident.clone(), sst_expr.typ.clone())?;
            Ok(sst::Statement::VarDecl(var, sst_expr))
        }
    }
}

fn analyze_block(
    parent: Rc<Scope>,
    block: &ast::Block,
) -> Result<Vec<sst::Statement>> {
    let scope = Scope::from_parent(parent);

    let mut sst_stmts = Vec::<sst::Statement>::new();
    for stmt in block {
        sst_stmts.push(analyze_statement(scope.clone(), stmt)?);
    }

    Ok(sst_stmts)
}

fn analyze_func_decl(
    ctx: &mut Context,
    fd: &ast::FuncDecl,
) -> Result<()> {
    let name = ident_to_name(&fd.signature.ident);
    if ctx.decls.contains_key(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    let params = analyze_field_decls(&ctx, &fd.signature.params)?;
    let ret = get_type(&ctx, &fd.signature.ret)?;

    let frame = StackFrame::new(ctx);
    let root = Scope::new(frame.clone());
    let stmts = analyze_block(root, &fd.body)?;

    let func = Rc::new(sst::Function{
        signature: Rc::new(sst::FuncSignature{
            name: name.clone(),
            params,
            ret,
        }),
        body: stmts,
        stack_size: 0,
    });

    ctx.decls.insert(name, sst::Declaration::Function(func));
    Ok(())
}

fn analyze_extern_func_decl(
    ctx: &mut Context,
    efd: &ast::FuncSignature,
) -> Result<()> {
    let name = ident_to_name(&efd.ident);
    if ctx.decls.contains_key(&name) {
        return Err(AnalysisError::MultipleDefinitions(name));
    }

    let params = analyze_field_decls(&ctx, &efd.params)?;
    let ret = get_type(&ctx, &efd.ret)?;

    let extern_func = Rc::new(sst::FuncSignature{
        name: name.clone(),
        params,
        ret,
    });

    ctx.decls.insert(name, sst::Declaration::ExternFunc(extern_func));
    Ok(())
}

pub fn program(prog: &ast::Program) -> Result<()> {
    let mut ctx = Context{
        decls: HashMap::new(),
    };

    ctx.add_primitive("void", 0, sst::Primitive::Void);
    ctx.add_primitive("byte", 1, sst::Primitive::UInt);
    ctx.add_primitive("short", 2, sst::Primitive::Int);
    ctx.add_primitive("ushort", 2, sst::Primitive::UInt);
    ctx.add_primitive("int", 4, sst::Primitive::Int);
    ctx.add_primitive("uint", 4, sst::Primitive::UInt);
    ctx.add_primitive("long", 8, sst::Primitive::Int);
    ctx.add_primitive("ulong", 8, sst::Primitive::UInt);

    for decl in prog {
        let ctx = &mut ctx;
        match decl {
            ast::Declaration::Struct(sd) => analyze_struct_decl(ctx, sd),
            ast::Declaration::Func(fd) => analyze_func_decl(ctx, fd),
            ast::Declaration::ExternFunc(efd) => analyze_extern_func_decl(ctx, efd),
        }?;
    }

    for (name, decl) in &ctx.decls {
        eprintln!("::{}\n{:#?}\n", name, decl);
    }

    Ok(())
}
