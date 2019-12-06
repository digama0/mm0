mod environment;

use std::sync::Arc;
use std::path::PathBuf;
use std::collections::HashMap;
pub use environment::Environment;
pub use crate::parser::{ErrorLevel, BoxError};
use crate::parser::*;

pub type ElabError = ParseError;
type Result<T> = std::result::Result<T, ElabError>;

struct _Elaborator<'a> {
  ast: &'a AST,
  errors: Vec<ElabError>,
  idx: usize,
}

pub trait FileServer {
  type WaitToken;
  fn request_elab(&self, path: PathBuf, f: impl Fn(BoxError) -> ElabError) ->
    Result<(Arc<PathBuf>, Self::WaitToken)>;

  fn elaborate(&self, path: Arc<PathBuf>, ast: &AST, _old: Option<(usize, Environment)>) ->
      (Environment, Vec<Arc<PathBuf>>) {
    let mut toks = HashMap::<Span, Option<Self::WaitToken>>::new();
    let mut deps: Vec<Arc<PathBuf>> = Vec::new();
    let mut errors: Vec<ElabError> = Vec::new();
    for (sp, f) in &ast.imports {
      match path.join(f).canonicalize()
        .map_err(|e| ElabError::new(sp.clone(), Box::new(e)))
        .and_then(|p| self.request_elab(p, |e| ElabError::new(sp.clone(), e))) {
        Ok((buf, tok)) => { deps.push(buf); toks.insert(sp.clone(), Some(tok)); }
        Err(e) => { errors.push(e); toks.insert(sp.clone(), None); }
      }
    }
    // unimplemented!()
    (Environment {errors}, deps)
  }
}
