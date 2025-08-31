//! MMC parser - parses MMC source code into AST
//!
//! This is a simple recursive descent parser for the MMC language.
//! It tokenizes and parses in a single pass.

use crate::{FileSpan, Symbol, intern};
use crate::types::{Binop, Unop, Size, Spanned, VarId, IdxVec, ast::*};
use crate::build_ast::BuildAst;
use std::str::Chars;
use std::collections::HashMap;

/// Parser state
pub struct Parser<'a> {
    /// The source text
    source: &'a str,
    /// Current position in the source
    chars: Chars<'a>,
    /// Current position for error reporting
    pos: usize,
    /// Lookahead character
    current: Option<char>,
    /// AST builder for name resolution
    build_ast: BuildAst,
}

/// Parser error
#[derive(Debug, Clone)]
pub struct ParseError {
    pub pos: usize,
    pub msg: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parse error at position {}: {}", self.pos, self.msg)
    }
}

impl std::error::Error for ParseError {}

type Result<T> = std::result::Result<T, ParseError>;

impl<'a> Parser<'a> {
    /// Create a new parser for the given source
    pub fn new(source: &'a str) -> Self {
        let mut parser = Parser {
            source,
            chars: source.chars(),
            pos: 0,
            current: None,
            build_ast: BuildAst::default(),
        };
        parser.advance();
        parser
    }

    /// Get the current character
    fn peek(&self) -> Option<char> {
        self.current
    }

    /// Advance to the next character
    fn advance(&mut self) {
        if self.current.is_some() {
            self.pos += self.current.unwrap().len_utf8();
        }
        self.current = self.chars.next();
    }

    /// Skip whitespace and comments
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.advance();
            } else if ch == '/' && self.peek_next() == Some('/') {
                // Skip line comment
                self.advance(); // '/'
                self.advance(); // '/'
                while let Some(ch) = self.peek() {
                    self.advance();
                    if ch == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    /// Peek at the next character without advancing
    fn peek_next(&self) -> Option<char> {
        let mut chars = self.chars.clone();
        chars.next()
    }

    /// Check if we're at the end of input
    fn is_eof(&self) -> bool {
        self.peek().is_none()
    }

    /// Create a dummy span for the current position
    fn span(&self) -> FileSpan {
        FileSpan { file: Default::default(), span: self.pos..self.pos }
    }

    /// Create a spanned value
    fn spanned<T>(&self, value: T) -> Spanned<T> {
        Spanned { span: self.span(), k: value }
    }

    /// Parse error at current position
    fn error(&self, msg: impl Into<String>) -> ParseError {
        ParseError { pos: self.pos, msg: msg.into() }
    }

    /// Expect a specific character
    fn expect(&mut self, ch: char) -> Result<()> {
        self.skip_whitespace();
        if self.peek() == Some(ch) {
            self.advance();
            Ok(())
        } else {
            Err(self.error(format!("Expected '{}', found {:?}", ch, self.peek())))
        }
    }

    /// Parse an identifier
    fn parse_ident(&mut self) -> Result<Symbol> {
        self.skip_whitespace();
        let start = self.pos;
        
        // First character must be alphabetic or underscore
        match self.peek() {
            Some(ch) if ch.is_alphabetic() || ch == '_' => self.advance(),
            _ => return Err(self.error("Expected identifier")),
        }

        // Subsequent characters can be alphanumeric or underscore
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let ident = &self.source[start..self.pos];
        Ok(intern(ident))
    }

    /// Parse a number
    fn parse_number(&mut self) -> Result<num::BigInt> {
        self.skip_whitespace();
        let start = self.pos;
        
        while let Some(ch) = self.peek() {
            if ch.is_numeric() {
                self.advance();
            } else {
                break;
            }
        }

        let num_str = &self.source[start..self.pos];
        num_str.parse().map_err(|_| self.error("Invalid number"))
    }

    /// Parse a type
    fn parse_type(&mut self) -> Result<Type> {
        self.skip_whitespace();
        
        // For now, support basic types
        let ty = match self.peek() {
            Some('i') => {
                let ident = self.parse_ident()?;
                match ident.0.as_ref() {
                    "i8" => TypeKind::Int(Size::S8),
                    "i16" => TypeKind::Int(Size::S16),
                    "i32" => TypeKind::Int(Size::S32),
                    "i64" => TypeKind::Int(Size::S64),
                    _ => return Err(self.error(format!("Unknown type: {}", ident.0))),
                }
            }
            Some('u') => {
                let ident = self.parse_ident()?;
                match ident.0.as_ref() {
                    "u8" => TypeKind::UInt(Size::S8),
                    "u16" => TypeKind::UInt(Size::S16),
                    "u32" => TypeKind::UInt(Size::S32),
                    "u64" => TypeKind::UInt(Size::S64),
                    _ => return Err(self.error(format!("Unknown type: {}", ident.0))),
                }
            }
            Some('v') => {
                let ident = self.parse_ident()?;
                if ident.0.as_ref() == "void" {
                    TypeKind::Void
                } else {
                    return Err(self.error(format!("Unknown type: {}", ident.0)));
                }
            }
            _ => return Err(self.error("Expected type")),
        };

        Ok(self.spanned(ty))
    }

    /// Parse an expression
    fn parse_expr(&mut self) -> Result<Expr> {
        self.parse_add_expr()
    }

    /// Parse addition/subtraction expression
    fn parse_add_expr(&mut self) -> Result<Expr> {
        let mut left = self.parse_mul_expr()?;

        loop {
            self.skip_whitespace();
            let op = match self.peek() {
                Some('+') => {
                    self.advance();
                    Binop::Add
                }
                Some('-') => {
                    self.advance();
                    Binop::Sub
                }
                _ => break,
            };

            let right = self.parse_mul_expr()?;
            left = self.spanned(ExprKind::Binop(op, Box::new(left), Box::new(right)));
        }

        Ok(left)
    }

    /// Parse multiplication/division expression
    fn parse_mul_expr(&mut self) -> Result<Expr> {
        let mut left = self.parse_primary_expr()?;

        loop {
            self.skip_whitespace();
            let op = match self.peek() {
                Some('*') => {
                    self.advance();
                    Binop::Mul
                }
                Some('/') => {
                    self.advance();
                    Binop::Div
                }
                _ => break,
            };

            let right = self.parse_primary_expr()?;
            left = self.spanned(ExprKind::Binop(op, Box::new(left), Box::new(right)));
        }

        Ok(left)
    }

    /// Parse primary expression
    fn parse_primary_expr(&mut self) -> Result<Expr> {
        self.skip_whitespace();

        match self.peek() {
            Some('(') => {
                self.advance();
                let expr = self.parse_expr()?;
                self.expect(')')?;
                Ok(expr)
            }
            Some(ch) if ch.is_numeric() => {
                let num = self.parse_number()?;
                Ok(self.spanned(ExprKind::Int(num)))
            }
            Some(ch) if ch.is_alphabetic() || ch == '_' => {
                let name = self.parse_ident()?;
                
                // Check for function call
                self.skip_whitespace();
                if self.peek() == Some('(') {
                    self.advance();
                    let mut args = Vec::new();
                    
                    // Parse arguments
                    self.skip_whitespace();
                    if self.peek() != Some(')') {
                        loop {
                            args.push(self.parse_expr()?);
                            self.skip_whitespace();
                            
                            if self.peek() == Some(',') {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                    }
                    
                    self.expect(')')?;
                    Ok(self.spanned(ExprKind::Call {
                        f: self.spanned(name),
                        tys: Box::new([]),
                        args: args.into_boxed_slice(),
                        variant: None,
                    }))
                } else {
                    // Variable reference
                    if let Some(var) = self.build_ast.find_var(name) {
                        Ok(self.spanned(ExprKind::Var(var)))
                    } else {
                        Ok(self.spanned(ExprKind::Unit))  // Placeholder for unresolved names
                    }
                }
            }
            _ => Err(self.error("Expected expression")),
        }
    }

    /// Parse a statement
    fn parse_stmt(&mut self) -> Result<Stmt> {
        self.skip_whitespace();

        // Check for 'let' statement
        if self.peek() == Some('l') && self.peek_keyword("let") {
            self.parse_keyword("let")?;
            
            let name = self.spanned(self.parse_ident()?);
            
            self.expect(':')?;
            let ty = self.parse_type()?;
            
            self.expect('=')?;
            let expr = self.parse_expr()?;
            
            self.expect(';')?;
            
            let var = self.build_ast.push_fresh(name.clone());
            Ok(self.spanned(StmtKind::Let {
                lhs: name.map_into(|n| TuplePatternKind::Typed(
                    Box::new(name.clone().map_into(|_| TuplePatternKind::Name(false, n, var))),
                    Box::new(ty)
                )),
                rhs: expr,
            }))
        }
        // Check for 'return' statement
        else if self.peek() == Some('r') && self.peek_keyword("return") {
            self.parse_keyword("return")?;
            
            let expr = if self.peek() == Some(';') {
                self.spanned(ExprKind::Unit)
            } else {
                self.parse_expr()?
            };
            
            self.expect(';')?;
            Ok(self.spanned(StmtKind::Return(expr)))
        }
        // Expression statement
        else {
            let expr = self.parse_expr()?;
            self.expect(';')?;
            Ok(self.spanned(StmtKind::Expr(expr.k)))
        }
    }

    /// Check if the next characters form a keyword
    fn peek_keyword(&self, keyword: &str) -> bool {
        let mut chars = self.chars.clone();
        let mut pos = self.pos;
        
        for expected in keyword.chars() {
            match self.source[pos..].chars().next() {
                Some(ch) if ch == expected => {
                    pos += ch.len_utf8();
                }
                _ => return false,
            }
        }
        
        // Check that keyword is followed by non-identifier character
        match self.source[pos..].chars().next() {
            Some(ch) if ch.is_alphanumeric() || ch == '_' => false,
            _ => true,
        }
    }

    /// Parse a keyword
    fn parse_keyword(&mut self, keyword: &str) -> Result<()> {
        for expected in keyword.chars() {
            if self.peek() == Some(expected) {
                self.advance();
            } else {
                return Err(self.error(format!("Expected keyword '{}'", keyword)));
            }
        }
        Ok(())
    }

    /// Parse a block
    fn parse_block(&mut self) -> Result<Block> {
        self.expect('{')?;
        
        let mut stmts = Vec::new();
        let mut expr = None;
        
        loop {
            self.skip_whitespace();
            
            if self.peek() == Some('}') {
                self.advance();
                break;
            }
            
            // Check if this might be the final expression (no semicolon)
            let stmt_start = self.pos;
            let stmt = self.parse_stmt();
            
            match stmt {
                Ok(stmt) => stmts.push(stmt),
                Err(_) => {
                    // Try parsing as expression without semicolon
                    self.pos = stmt_start;
                    self.chars = self.source[stmt_start..].chars();
                    self.current = self.chars.clone().next();
                    
                    let e = self.parse_expr()?;
                    self.skip_whitespace();
                    
                    if self.peek() == Some('}') {
                        expr = Some(e);
                        self.advance();
                        break;
                    } else {
                        return Err(self.error("Expected '}' or ';'"));
                    }
                }
            }
        }
        
        Ok(Block { stmts, expr })
    }

    /// Parse function arguments
    fn parse_args(&mut self) -> Result<Vec<(Spanned<Symbol>, Type)>> {
        self.expect('(')?;
        
        let mut args = Vec::new();
        
        self.skip_whitespace();
        if self.peek() != Some(')') {
            loop {
                let name = self.spanned(self.parse_ident()?);
                self.expect(':')?;
                let ty = self.parse_type()?;
                
                args.push((name, ty));
                
                self.skip_whitespace();
                if self.peek() == Some(',') {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        
        self.expect(')')?;
        Ok(args)
    }

    /// Parse a procedure
    fn parse_proc(&mut self) -> Result<Item> {
        self.parse_keyword("proc")?;
        
        let name = self.spanned(self.parse_ident()?);
        let args = self.parse_args()?;
        
        // Parse return type
        self.skip_whitespace();
        let (outs, rets) = if self.peek() == Some('-') {
            self.advance();
            self.expect('>')?;
            
            let ret_ty = self.parse_type()?;
            let ret_name = self.spanned(intern("ret"));
            (vec![(ret_name, ret_ty.clone())], vec![ret_ty])
        } else {
            (vec![], vec![])
        };

        // Enter scope for function body
        let body = self.build_ast.with_ctx(|ctx| {
            // Add arguments to scope
            let mut arg_vars = Vec::new();
            for (name, ty) in &args {
                let var = ctx.push_fresh(name.clone());
                arg_vars.push(Arg { name: self.spanned(true), kind: ArgKind::Lam(name.map_into(|n| (n, var))) });
            }
            
            ctx.parse_block()
        })?;

        // Convert args to the expected format
        let arg_specs: Vec<_> = args.into_iter().enumerate().map(|(i, (name, ty))| {
            Arg {
                name: self.spanned(true),
                kind: ArgKind::Lam(name.map_into(|n| (n, VarId(i as u32)))),
            }
        }).collect();

        // Determine if this is main
        let is_main = name.k.0 == "main";
        
        Ok(self.spanned(ItemKind::Proc {
            intrinsic: None,
            kind: if is_main { ProcKind::Main } else { ProcKind::Func },
            name,
            tyargs: 0,
            args: arg_specs.into_boxed_slice(),
            outs: outs.into_iter().map(|(name, ty)| Arg {
                name: self.spanned(false),
                kind: ArgKind::Lam(name.map_into(|n| (n, VarId(1000)))), // Placeholder
            }).collect::<Vec<_>>().into_boxed_slice(),
            rets: rets.into_boxed_slice(),
            variant: None,
            body,
        }))
    }

    /// Parse a top-level item
    fn parse_item(&mut self) -> Result<Item> {
        self.skip_whitespace();
        
        if self.peek() == Some('p') && self.peek_keyword("proc") {
            self.parse_proc()
        } else {
            Err(self.error("Expected 'proc'"))
        }
    }

    /// Parse the entire file
    pub fn parse(mut self) -> Result<(Vec<Item>, IdxVec<VarId, Spanned<Symbol>>)> {
        let mut items = Vec::new();
        
        while !self.is_eof() {
            self.skip_whitespace();
            if self.is_eof() {
                break;
            }
            
            items.push(self.parse_item()?);
        }
        
        Ok((items, self.build_ast.var_names))
    }
}

impl BuildAst {
    /// Helper to find a variable by name
    fn find_var(&self, name: Symbol) -> Option<VarId> {
        self.name_map.get(&name).and_then(|vars| vars.last()).copied()
    }
}

/// Parse MMC source code into AST
pub fn parse_mmc(source: &str) -> Result<(Vec<Item>, IdxVec<VarId, Spanned<Symbol>>)> {
    Parser::new(source).parse()
}