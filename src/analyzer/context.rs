use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::sst;
use crate::parser::ast;

pub struct Types {
    pub void: Rc<sst::Type>,
    pub bool: Rc<sst::Type>,
    pub byte: Rc<sst::Type>,
    pub short: Rc<sst::Type>,
    pub ushort: Rc<sst::Type>,
    pub int: Rc<sst::Type>,
    pub uint: Rc<sst::Type>,
    pub long: Rc<sst::Type>,
    pub ulong: Rc<sst::Type>,
    pub float: Rc<sst::Type>,
    pub double: Rc<sst::Type>,
    pub voidptr: Rc<sst::Type>,
    pub byteptr: Rc<sst::Type>,
}

pub struct Context {
    pub types: Types,
    pub underscore: Rc<String>,
    decls: RefCell<HashMap<Rc<String>, sst::Declaration>>,
    struct_templates: RefCell<HashMap<Rc<String>, Rc<ast::StructDecl>>>,
    string_constant_map: RefCell<HashMap<Rc<String>, sst::StringConstant>>,
    string_constants: RefCell<Vec<(sst::StringConstant, Rc<String>)>>,
    methods: RefCell<HashMap<Rc<String>, Rc<sst::FuncSignature>>>,
}

impl Context {
    pub fn new(types: Types) -> Self {
        let ctx = Self {
            decls: RefCell::new(HashMap::new()),
            underscore: Rc::new("_".to_owned()),
            types,
            struct_templates: RefCell::new(HashMap::new()),
            string_constant_map: RefCell::new(HashMap::new()),
            string_constants: RefCell::new(Vec::new()),
            methods: RefCell::new(HashMap::new()),
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
        ctx.add_type(ctx.types.byteptr.clone());
        ctx.add_type(ctx.types.voidptr.clone());

        ctx
    }

    pub fn done(self) -> Vec<(sst::StringConstant, Rc<String>)> {
        self.string_constants.take()
    }

    pub fn add_type(&self, typ: Rc<sst::Type>) {
        self.decls
            .borrow_mut()
            .insert(typ.name.clone(), sst::Declaration::Type(typ));
    }

    pub fn add_string(&self, str: &Rc<String>) -> sst::StringConstant {
        let mut string_map = self.string_constant_map.borrow_mut();
        if let Some(sc) = string_map.get(str) {
            return *sc;
        }

        let mut strings = self.string_constants.borrow_mut();
        let sc = sst::StringConstant {
            index: self.string_constants.borrow().len() as u32,
        };
        string_map.insert(str.clone(), sc);
        strings.push((sc, str.clone()));
        sc
    }

    pub fn get_decl(&self, name: &Rc<String>) -> Option<sst::Declaration> {
        self.decls.borrow().get(name).map(|x| x.clone())
    }

    pub fn has_decl(&self, name: &Rc<String>) -> bool {
        self.decls.borrow().contains_key(name)
    }

    pub fn add_decl(&self, name: Rc<String>, decl: sst::Declaration) {
        self.decls.borrow_mut().insert(name, decl);
    }

    pub fn get_struct_template(&self, name: &Rc<String>) -> Option<Rc<ast::StructDecl>> {
        self.struct_templates.borrow().get(name).map(|x| x.clone())
    }

    pub fn has_struct_template(&self, name: &Rc<String>) -> bool {
        self.struct_templates.borrow().contains_key(name)
    }

    pub fn add_struct_template(&self, name: Rc<String>, tmpl: ast::StructDecl) {
        self.struct_templates
            .borrow_mut()
            .insert(name, Rc::new(tmpl));
    }

    pub fn add_method(&self, typ: &Rc<sst::Type>, sig: Rc<sst::FuncSignature>) {
        self.methods.borrow_mut().insert(typ.name.clone(), sig);
    }
}
