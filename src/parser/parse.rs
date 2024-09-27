use std::fmt::Display;
use std::rc::Rc;

use super::ast;
use super::reader::{Reader, SeekPoint};

#[derive(Clone, Copy)]
pub enum ErrorKind {
    UnexpectedEOF,
    UnexpectedChar(u8),
    ExpectedChar(u8),
    BadKeyword,
    NoMatchingParse,
}

impl Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ErrorKind::UnexpectedEOF => write!(f, "Unexpected EOF"),
            ErrorKind::UnexpectedChar(ch) => write!(f, "Unexpected char '{}'", ch as char),
            ErrorKind::ExpectedChar(ch) => write!(f, "Expected '{}'", ch as char),
            ErrorKind::BadKeyword => write!(f, "Expected a keyword"),
            ErrorKind::NoMatchingParse => write!(f, "No matching parse"),
        }
    }
}

#[derive(Clone, Copy)]
pub struct ParseError {
    pub line: u32,
    pub col: u32,
    pub kind: ErrorKind,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.kind)
    }
}

impl ParseError {
    fn new(r: &Reader, kind: ErrorKind) -> Self {
        Self {
            line: r.line,
            col: r.col,
            kind,
        }
    }

    fn unexpected_eof(r: &Reader) -> Self {
        Self::new(r, ErrorKind::UnexpectedEOF)
    }

    fn unexpected_char(r: &Reader, ch: u8) -> Self {
        Self::new(r, ErrorKind::UnexpectedChar(ch))
    }

    fn unexpected_maybe(r: &Reader, ch: Option<u8>) -> Self {
        if let Some(ch) = ch {
            Self::unexpected_char(r, ch)
        } else {
            Self::unexpected_eof(r)
        }
    }

    fn expected_char(r: &Reader, ch: u8) -> Self {
        Self::new(r, ErrorKind::ExpectedChar(ch))
    }

    fn bad_keyword(r: &Reader) -> Self {
        Self::new(r, ErrorKind::BadKeyword)
    }

    fn unexpected_peek(r: &Reader) -> Self {
        Self::unexpected_maybe(r, r.peek())
    }
}

type Result<T> = std::result::Result<T, ParseError>;

struct Combinator<'a, 'b> {
    r: &'a mut Reader<'b>,
    error: Option<ParseError>,
    point: SeekPoint,
}

impl<'a, 'b> Combinator<'a, 'b> {
    fn new(r: &'a mut Reader<'b>) -> Self {
        whitespace(r);
        let point = r.tell();
        Self {
            r,
            error: None,
            point,
        }
    }

    fn consider_error(&mut self, new_err: ParseError) {
        let Some(err) = self.error else {
            self.error = Some(new_err);
            return;
        };

        if new_err.line > err.line {
            self.error = Some(new_err);
        } else if new_err.line == err.line && new_err.col > err.col {
            self.error = Some(new_err);
        }
    }

    fn err(&mut self) -> ParseError {
        self.r.seek(self.point);
        if let Some(err) = self.error {
            err
        } else {
            ParseError::new(self.r, ErrorKind::NoMatchingParse)
        }
    }
}

macro_rules! try_parse {
    ($c: tt, $func: tt) => {
        $c.r.seek($c.point);
        match $func($c.r) {
            Ok(ok) => return Ok(ok),
            Err(err) => $c.consider_error(err),
        };
    }
}

fn is_alpha(ch: u8) -> bool {
    (ch >= b'a' && ch <= b'z') || (ch >= b'A' && ch <= b'Z')
}

fn is_alnum(ch: u8) -> bool {
    is_alpha(ch) || (ch >= b'0' && ch <= b'9')
}

/// Comment ::= '#' [^\\n]*
fn comment(r: &mut Reader) {
    r.consume(); // '#'
    while !r.eof() && r.peek() != Some(b'\n') {
        r.consume();
    }
}

/// Whitespace ::= ('\\t' | '\\n' | '\\r' | [space] | Comment)*
pub fn whitespace(r: &mut Reader) {
    loop {
        let Some(ch) = r.peek() else {
            return;
        };

        if ch == b'#' {
            comment(r);
        } else if ch == b'\t' || ch == b'\n' || ch == b'\r' || ch == b' ' {
            r.consume();
        } else {
            return;
        }
    }
}

/// Ident ::= [a-zA-Z_][a-zA-Z0-9_]*
pub fn identifier(r: &mut Reader) -> Result<ast::Ident> {
    whitespace(r);

    let mut ident = String::new();

    let Some(ch) = r.peek() else {
        return Err(ParseError::unexpected_eof(r));
    };

    if !is_alpha(ch) {
        return Err(ParseError::unexpected_char(r, ch));
    }
    ident.push(ch as char);
    r.consume();

    loop {
        let Some(ch) = r.peek() else {
            return Err(ParseError::unexpected_eof(r));
        };

        if !is_alnum(ch) {
            return Ok(Rc::new(ident));
        }

        ident.push(ch as char);
        r.consume();
    };
}

/// QualifiedIdent ::= Ident | Ident '::' QualifiedIdent
pub fn qualified_ident(r: &mut Reader) -> Result<ast::QualifiedIdent> {
    whitespace(r);
    let ident = identifier(r)?;

    let mut idents = ast::QualifiedIdent::new();
    idents.push(ident);

    loop {
        whitespace(r);
        if r.peek_cmp_consume(b"::") {
            idents.push(identifier(r)?);
        } else {
            return Ok(idents);
        }
    }
}

/// TypeParams ::= QualifiedIdent | (QualifiedIdent ',' TypeParams)
/// TypeSpec ::= QualifiedIdent ('[' TypeParams ']')?
pub fn type_spec(r: &mut Reader) -> Result<ast::TypeSpec> {
    whitespace(r);
    let ident = qualified_ident(r)?;
    let mut params = Vec::<ast::TypeParam>::new();

    if r.peek_cmp_consume(b"[") {
        loop {
            params.push(ast::TypeParam::Type(Box::new(type_spec(r)?)));

            whitespace(r);
            let ch = r.peek();
            if r.peek_cmp_consume(b"]") {
                break;
            } else if !r.peek_cmp_consume(b",") {
                return Err(ParseError::unexpected_maybe(r, ch));
            }
        }
    }

    Ok(ast::TypeSpec{ident, params})
}

/// ExprList ::= (Expression ',')* (Expression ','?)?
pub fn expr_list(r: &mut Reader) -> Result<Vec<ast::Expression>> {
    let mut exprs = Vec::<ast::Expression>::new();

    loop {
        let point = r.tell();
        let Ok(expr) = expression(r) else {
            r.seek(point);
            return Ok(exprs);
        };

        exprs.push(expr);
        whitespace(r);

        if !r.peek_cmp_consume(b",") {
            return Ok(exprs);
        }
    }
}

/// FuncCallExpr ::= QualifiedIdent '(' ExprList ')'
pub fn func_call_expr(r: &mut Reader) -> Result<ast::Expression> {
    let ident = qualified_ident(r)?;

    if !r.peek_cmp_consume(b"(") {
        return Err(ParseError::unexpected_peek(r));
    }

    let exprs = expr_list(r)?;

    if !r.peek_cmp_consume(b")") {
        return Err(ParseError::unexpected_peek(r));
    }

    Ok(ast::Expression::FuncCall(ident, exprs))
}

/// AssignExpr ::= Ident '=' Expression
pub fn assign_expr(r: &mut Reader) -> Result<ast::Expression> {
    let ident = identifier(r)?;

    whitespace(r);
    if !r.peek_cmp_consume(b"=") {
        return Err(ParseError::unexpected_peek(r));
    }

    let expr = expression(r)?;

    Ok(ast::Expression::Assignment(ident, Box::new(expr)))
}

/// UninitializedExpr ::= 'uninitialized' TypeSpec?
pub fn uninitialized_expr(r: &mut Reader) -> Result<ast::Expression> {
    let ident = identifier(r)?;
    if ident.as_str() != "uninitialized" {
        return Err(ParseError::bad_keyword(r));
    }

    whitespace(r);

    let point = r.tell();
    let Ok(typ) = type_spec(r) else {
        r.seek(point);
        return Ok(ast::Expression::Uninitialized(None));
    };

    Ok(ast::Expression::Uninitialized(Some(typ)))
}

/// VariableExpr ::= Ident
pub fn variable_expr(r: &mut Reader) -> Result<ast::Expression> {
    let ident = identifier(r)?;
    Ok(ast::Expression::Variable(ident))
}

/// GroupExpr ::= '(' Expression ')'
pub fn group_expr(r: &mut Reader) -> Result<ast::Expression> {
    if !r.peek_cmp_consume(b"(") {
        return Err(ParseError::unexpected_peek(r));
    }

    let expr = expression(r)?;

    if !r.peek_cmp_consume(b")") {
        return Err(ParseError::unexpected_peek(r));
    }

    Ok(expr)
}

/// Expression ::=
///     FuncCallExpr |
///     AssignExpr |
///     UninitializedExpr |
///     GroupExpr |
///     VariableExpr
pub fn expression(r: &mut Reader) -> Result<ast::Expression> {
    let mut comb = Combinator::new(r);

    try_parse!(comb, func_call_expr);
    try_parse!(comb, assign_expr);
    try_parse!(comb, uninitialized_expr);
    try_parse!(comb, group_expr);
    try_parse!(comb, variable_expr);

    Err(comb.err())
}

/// VarDeclStmt ::= Ident ':=' Expression
fn var_decl_stmt(r: &mut Reader) -> Result<ast::Statement> {
    let name = identifier(r)?;

    whitespace(r);
    if !r.peek_cmp_consume(b":=") {
        return Err(ParseError::unexpected_peek(r));
    }

    let expr = expression(r)?;
    Ok(ast::Statement::VarDecl(name, Box::new(expr)))
}

/// ExpressionStmt ::= Expression
fn expression_stmt(r: &mut Reader) -> Result<ast::Statement> {
    let expr = expression(r)?;
    Ok(ast::Statement::Expression(Box::new(expr)))
}

/// Statement ::=
///     VarDeclStmt |
///     ExpressionStmt
pub fn statement(r: &mut Reader) -> Result<ast::Statement> {
    let mut comb = Combinator::new(r);

    try_parse!(comb, var_decl_stmt);
    try_parse!(comb, expression_stmt);

    Err(comb.err())
}

/// Block ::= Statement | (Statement ';' Block)
pub fn block(r: &mut Reader) -> Result<ast::Block> {
    whitespace(r);

    let mut block = ast::Block::new();

    if !r.peek_cmp_consume(b"{") {
        return Err(ParseError::unexpected_peek(r));
    }

    loop {
        whitespace(r);

        if r.peek_cmp_consume(b"}") {
            return Ok(block);
        }

        block.push(statement(r)?);
        if !r.peek_cmp_consume(b";") {
            return Err(ParseError::expected_char(r, b';'));
        }
    }
}

/// FieldDecl ::= (Ident ':')? TypeSpec
pub fn field_decl(r: &mut Reader) -> Result<ast::FieldDecl> {
    whitespace(r);

    let point = r.tell();
    let ident = identifier(r)?;
    whitespace(r);

    if r.peek_n(0) == Some(b':') && r.peek_n(1) != Some(b':') {
        // If the next character is a single colon,
        // then we parsed the name and a type spec follows
        r.consume(); // ':'
        let typ = type_spec(r)?;
        Ok(ast::FieldDecl{name: ident, typ})
    } else {
        // If the next character is not a single colon,
        // the (Ident ':') part is missing, and we need to rewind
        // and parse a type_spec and use '_' as the name
        r.seek(point);
        let typ = type_spec(r)?;
        Ok(ast::FieldDecl{name: Rc::new("_".into()), typ})
    }
}

/// FieldDecls ::= (FieldDecl ',')* (FieldDecl ','?)?
pub fn field_decls(r: &mut Reader) -> Result<Vec<ast::FieldDecl>> {
    let mut decls = Vec::<ast::FieldDecl>::new();

    loop {
        let point = r.tell();
        let Ok(decl) = field_decl(r) else {
            r.seek(point);
            return Ok(decls);
        };

        decls.push(decl);
        whitespace(r);

        if !r.peek_cmp_consume(b",") {
            return Ok(decls);
        }
    }
}

/// StructDecl ::= 'struct' Ident '{' FieldDecls '}'
fn struct_decl(r: &mut Reader) -> Result<ast::Declaration> {
    let intro = identifier(r)?;
    if intro.as_str() != "struct" {
        return Err(ParseError::bad_keyword(r));
    }

    let name = identifier(r)?;
    whitespace(r);

    if !r.peek_cmp_consume(b"{") {
        return Err(ParseError::expected_char(r, b'{'));
    }

    let fields = field_decls(r)?;
    whitespace(r);

    if !r.peek_cmp_consume(b"}") {
        return Err(ParseError::expected_char(r, b'{'));
    }

    Ok(ast::Declaration::Struct(ast::StructDecl{name, fields}))
}

/// FuncSignature ::= 'func' QualifiedIdent '(' FieldDecls ')' TypeSpec
fn func_signature(r: &mut Reader) -> Result<ast::FuncSignature> {
    let intro = identifier(r)?;
    if intro.as_str() != "func" {
        return Err(ParseError::bad_keyword(r));
    }

    let ident = qualified_ident(r)?;

    if !r.peek_cmp_consume(b"(") {
        return Err(ParseError::expected_char(r, b'('));
    }

    let params = field_decls(r)?;

    if !r.peek_cmp_consume(b")") {
        return Err(ParseError::expected_char(r, b')'));
    }

    let ret = type_spec(r)?;
    Ok(ast::FuncSignature{ident, params, ret})
}

/// FuncDecl ::= FuncSignature Block
fn func_decl(r: &mut Reader) -> Result<ast::Declaration> {
    let signature = func_signature(r)?;
    let body = block(r)?;
    Ok(ast::Declaration::Func(ast::FuncDecl{signature, body}))
}

/// ExternFuncDecl ::= 'extern' FuncSignature ';'
fn extern_func_decl(r: &mut Reader) -> Result<ast::Declaration> {
    let intro = identifier(r)?;
    if intro.as_str() != "extern" {
        return Err(ParseError::bad_keyword(r));
    }

    let signature = func_signature(r)?;
    whitespace(r);
    if !r.peek_cmp_consume(b";") {
        return Err(ParseError::expected_char(r, b';'));
    }

    Ok(ast::Declaration::ExternFunc(signature))
}

/// Declaration ::= StructDecl | FuncDecl | ExternFuncDecl
pub fn declaration(r: &mut Reader) -> Result<ast::Declaration> {
    let mut comb = Combinator::new(r);

    try_parse!(comb, struct_decl);
    try_parse!(comb, func_decl);
    try_parse!(comb, extern_func_decl);

    Err(comb.err())
}

/// Program ::= Declaration*
pub fn program(r: &mut Reader) -> Result<ast::Program> {
    let mut program = ast::Program::new();

    loop {
        whitespace(r);
        if r.eof() {
            return Ok(program);
        }

        program.push(declaration(r)?);
    }
}
