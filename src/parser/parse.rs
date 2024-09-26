use super::ast;
use super::reader::Reader;

#[derive(Debug, Clone)]
pub struct ParseError {
    pub filename: String,
    pub line: u32,
    pub col: u32,
    pub msg: String,
}

type Result<T> = std::result::Result<T, ParseError>;

macro_rules! err {
    ($r: ident, $($msg: tt)*) => {
        Err(ParseError{
            filename: $r.filename.clone(),
            line: $r.line,
            col: $r.col,
            msg: format!($($msg)*),
        })
    }
}

fn is_alpha(ch: u8) -> bool {
    (ch >= b'a' && ch <= b'z') || (ch >= b'A' && ch <= b'Z')
}

fn is_alnum(ch: u8) -> bool {
    is_alpha(ch) || (ch >= b'0' && ch <= b'9')
}

/// Comment ::= '#' [^\n]*
fn comment(r: &mut Reader) {
    r.consume(); // '#'
    while !r.eof() && r.peek() != Some(b'\n') {
        r.consume();
    }
}

/// Whitespace ::= ('\t' | '\n' | '\r' | ' ' | Comment)*
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

/// Ident ::= [a-zA-Z][a-zA-Z0-9]
pub fn identifier(r: &mut Reader) -> Result<ast::Ident> {
    whitespace(r);

    let mut ident = ast::Ident::new();

    let Some(ch) = r.peek() else {
        return err!(r, "Unexpected EOF");
    };

    if !is_alpha(ch) {
        return err!(
            r, "Non-alphabetic character at the start of identifier: '{}'", ch as char
        );
    }
    ident.push(ch as char);
    r.consume();

    loop {
        let Some(ch) = r.peek() else {
            return Ok(ident);
        };

        if !is_alnum(ch) {
            return Ok(ident);
        }

        ident.push(ch as char);
        r.consume();
    };
}

fn qualified_ident_after_ident(
    r: &mut Reader,
    ident: ast::Ident,
) -> Result<ast::QualifiedIdent> {
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

/// QualifiedIdent ::= Ident | (Ident '::' QualifiedIdent)
pub fn qualified_ident(r: &mut Reader) -> Result<ast::QualifiedIdent> {
    whitespace(r);
    let ident = identifier(r)?;
    qualified_ident_after_ident(r, ident)
}

fn type_spec_after_ident(r: &mut Reader, ident: ast::Ident) -> Result<ast::TypeSpec> {
    let ident = qualified_ident_after_ident(r, ident)?;
    let mut params = Vec::<ast::QualifiedIdent>::new();

    if r.peek_cmp_consume(b"[") {
        loop {
            params.push(qualified_ident(r)?);

            whitespace(r);
            let ch = r.peek();
            if r.peek_cmp_consume(b"]") {
                break;
            } else if !r.peek_cmp_consume(b",") {
                return err!(r, "Expected ',' or ']', got {:?}", ch);
            }
        }
    }

    Ok(ast::TypeSpec{ident, params})
}

/// TypeParams ::= QualifiedIdent | (QualifiedIdent ',' TypeParams)
/// TypeSpec ::= QualifiedIdent ('[' TypeParams ']')?
pub fn type_spec(r: &mut Reader) -> Result<ast::TypeSpec> {
    whitespace(r);
    let ident = identifier(r)?;
    type_spec_after_ident(r, ident)
}

/// TypeParam ::= TypeSpec
pub fn type_param(r: &mut Reader) -> Result<ast::TypeParam> {
    Ok(ast::TypeParam::Type(Box::new(type_spec(r)?)))
}

fn expression_after_ident(
    r: &mut Reader,
    ident: ast::Ident,
) -> Result<ast::Expression> {
    whitespace(r);

    if r.peek_cmp_consume(b"=") {
        Ok(ast::Expression::Assignment(ident, Box::new(expression(r)?)))
    } else if ident == "uninitialized" {
        let Some(ch) = r.peek() else {
            return Ok(ast::Expression::Uninitialized(None))
        };

        if is_alnum(ch) {
            Ok(ast::Expression::Uninitialized(Some(type_spec(r)?)))
        } else {
            Ok(ast::Expression::Uninitialized(None))
        }
    } else {
        Ok(ast::Expression::Variable(ident))
    }
}

/// VariableExpr ::= Ident
/// AssignExpr ::= Ident '=' Expression
/// UninitializedExpr ::= 'uninitialized'
/// GroupExpr ::= '(' Expression ')'
/// Expression ::= VariableExpr | AssignExpr | UninitializedExpr | GroupExpr
pub fn expression(r: &mut Reader) -> Result<ast::Expression> {
    whitespace(r);

    let Some(ch) = r.peek() else {
        return err!(r, "Unexpected EOF");
    };

    if is_alpha(ch) {
        let ident = identifier(r)?;
        expression_after_ident(r, ident)
    } else if ch == b'(' {
        r.consume(); // '('
                     //
        whitespace(r);
        let expr = Box::new(expression(r)?);

        whitespace(r);
        if !r.peek_cmp_consume(b")") {
            return err!(r, "Expected ')', got: {}", ch as char);
        }

        Ok(ast::Expression::Group(expr))
    } else {
        err!(r, "Unexpected character in expression: {}", ch as char)
    }
}

fn statement_after_ident(
    r: &mut Reader,
    ident: ast::Ident,
) -> Result<ast::Statement> {
    whitespace(r);

    if r.peek_cmp_consume(b":=") {
        let expr = Box::new(expression(r)?);
        Ok(ast::Statement::VarDecl(ident, expr))
    } else {
        let expr = Box::new(expression_after_ident(r, ident)?);
        Ok(ast::Statement::Expression(expr))
    }
}

/// ExpressionStmt ::= Expression
/// VarDeclStmt ::= Ident ':=' Expression
/// Statement ::= ExpressionStmt | VarDeclStmt
pub fn statement(r: &mut Reader) -> Result<ast::Statement> {
    whitespace(r);

    let Some(ch) = r.peek() else {
        return err!(r, "Unexpected EOF");
    };

    if is_alpha(ch) {
        let ident = identifier(r)?;
        statement_after_ident(r, ident)
    } else {
        let expr = Box::new(expression(r)?);
        Ok(ast::Statement::Expression(expr))
    }
}

/// Block ::= Statement | (Statement ';' Block)
pub fn block(r: &mut Reader) -> Result<ast::Block> {
    whitespace(r);

    let mut block = ast::Block::new();

    if !r.peek_cmp_consume(b"{") {
        return err!(r, "Expected '{{', got {:?}", r.peek());
    }

    loop {
        whitespace(r);

        if r.peek_cmp_consume(b"}") {
            return Ok(block);
        }

        block.push(statement(r)?);
        if !r.peek_cmp_consume(b";") {
            return err!(r, "Expected ';' after statement");
        }
    }
}

/// FieldDecl ::= Ident ':' TypeSpec
pub fn field_decl(r: &mut Reader) -> Result<ast::FieldDecl> {
    let ident = identifier(r)?;

    whitespace(r);
    if r.peek_n(0) == Some(b':') && r.peek_n(1) != Some(b':') {
        let typ = type_spec(r)?;
        Ok(ast::FieldDecl{name: ident, typ})
    } else {
        let typ = type_spec_after_ident(r, ident)?;
        Ok(ast::FieldDecl{name: "_".into(), typ})
    }
}

/// StructDecl ::= 'struct' Ident '{' FieldDecl* '}'
fn struct_decl_after_introducer(r: &mut Reader) -> Result<ast::StructDecl> {
    let name = identifier(r)?;

    if !r.peek_cmp_consume(b"{") {
        return err!(r, "Expected '{{'");
    }

    let mut fields = Vec::<ast::FieldDecl>::new();
    loop {
        whitespace(r);
        if r.peek_cmp_consume(b"}") {
            return Ok(ast::StructDecl{name, fields});
        }

        fields.push(field_decl(r)?);
    }
}

/// FuncSign ::= 'func' QualifiedIdent '(' FieldDecl* ')' TypeSpec
fn func_sign_after_introducer(r: &mut Reader) -> Result<ast::FuncSign> {
    let ident = qualified_ident(r)?;

    if !r.peek_cmp_consume(b"(") {
        return err!(r, "Expected '('");
    }

    let mut params = Vec::<ast::FieldDecl>::new();
    loop {
        whitespace(r);
        if r.peek_cmp_consume(b")") {
            break;
        }

        params.push(field_decl(r)?);
    }

    let ret = type_spec(r)?;
    Ok(ast::FuncSign{ident, params, ret})
}

/// FuncDecl ::= FuncSignature Block
fn func_decl_after_introducer(r: &mut Reader) -> Result<ast::FuncDecl> {
    let signature = func_sign_after_introducer(r)?;
    let body = block(r)?;
    Ok(ast::FuncDecl{signature, body})
}

// ExternFuncDecl ::= FuncSignature ';'
fn extern_func_decl_after_introducer(r: &mut Reader) -> Result<ast::FuncSign> {
    let signature = func_sign_after_introducer(r)?;
    whitespace(r);
    if !r.peek_cmp_consume(b";") {
        return err!(r, "Expected ';' after extern func");
    }

    Ok(signature)
}

/// Declaration ::= StructDecl | FuncDecl ExternFuncDecl
pub fn declaration(r: &mut Reader) -> Result<ast::Declaration> {
    let ident = identifier(r)?;
    if ident == "struct" {
        Ok(ast::Declaration::Struct(struct_decl_after_introducer(r)?))
    } else if ident == "func" {
        Ok(ast::Declaration::Func(func_decl_after_introducer(r)?))
    } else if ident == "extern" {
        let ident = identifier(r)?;
        if ident == "func" {
            Ok(ast::Declaration::ExternFunc(extern_func_decl_after_introducer(r)?))
        } else {
            err!(r, "Expected 'func', got: {}", ident)
        }
    } else {
        err!(r, "Expected top-level 'struct' or 'func', got: {}", ident)
    }
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
