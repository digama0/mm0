//! The compiler lemmas we need from `compiler.mm1`
use std::ops::Index;

macro_rules! make_predef {
  {$($(#[$attr:meta])* $x:ident: $e:expr,)*} => {make_predef!{map 0; ; $($(#[$attr])* $x: $e,)*}};
  {map $n:expr; $(($m:expr, $xm:ident, $em:expr))*; $(#[$attr:meta])* $x:ident: $e:expr, $($rest:tt)*} => {
    make_predef! {map $n+1; $(($m,$xm,$em))* ($n,$(#[$attr])* $x,$e); $($rest)*}
  };
  {map $n:expr; $(($m:expr, $(#[$attr:meta])* $x:ident, $e:expr))*;} => {
    /// A predef is a name of an external constant, defined in `compiler.mm1` and required
    /// for proof output.
    #[derive(Copy, Clone, Debug)]
    pub enum Predef { $(#[allow(unused)] $(#[$attr])* $x,)* }
    $crate::deep_size_0!(Predef);

    /// A map from [`Predef`] to `A`, implemented as an array.
    #[derive(Debug, DeepSizeOf)]
    pub struct PredefMap<A>([A; Predef::COUNT]);

    impl Predef {
      const COUNT: usize = $n;
    }

    impl<A> Index<Predef> for PredefMap<A> {
      type Output = A;
      fn index(&self, i: Predef) -> &A { &self.0[i as usize] }
    }

    #[allow(unused)]
    impl<A> PredefMap<A> {
      /// Map a function `f: &A -> B` to turn a `&PredefMap<A>` into a `PredefMap<B>`.
      pub fn map<'a, B>(&'a self, mut f: impl FnMut(&'a A) -> B) -> PredefMap<B> {
        PredefMap([$(f(&self.0[$m])),*])
      }

      /// Construct a `PredefMap<A>` from an initialization function `(Predef, &str) -> A`.
      pub fn new(mut f: impl FnMut(Predef, &'static str) -> A) -> Self {
        PredefMap([$(f(Predef::$x, $e)),*])
      }
    }
  };
}

make_predef! {
  /// `:sorry` is used to stub out missing proofs.
  Sorry: ":sorry",
}