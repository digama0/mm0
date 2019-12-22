
use super::*;

impl<'a, F: FileServer + ?Sized> Elaborator<'a, F> {
  pub fn refine(&mut self, sp: Span, es: Vec<LispVal>) -> Result<()> {
    Ok(())
  }
}
