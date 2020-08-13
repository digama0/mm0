use std::ops::Index;

macro_rules! make_predef {
  {$($x:ident: $e:expr,)*} => {make_predef!{map 0; ; $($x: $e,)*}};
  {map $n:expr; $(($m:expr, $xm:ident, $em:expr))*; $x:ident: $e:expr, $($xs:ident: $es:expr,)*} => {
    make_predef! {map $n+1; $(($m,$xm,$em))* ($n,$x,$e); $($xs: $es,)*}
  };
  {map $n:expr; $(($m:expr, $x:ident, $e:expr))*;} => {
    #[derive(Copy, Clone, Debug)] enum Predef { $(#[allow(unused)] $x,)* }

    #[derive(Debug)]
    pub struct PredefMap<A>([A; Predef::COUNT]);

    impl Predef {
      const COUNT: usize = $n;
    }

    impl<A> Index<Predef> for PredefMap<A> {
      type Output = A;
      fn index(&self, i: Predef) -> &A { &self.0[i as usize] }
    }

    impl<A> PredefMap<A> {
      pub fn map<'a, B>(&'a self, mut f: impl FnMut(&'a A) -> B) -> PredefMap<B> {
        PredefMap([$(f(&self.0[$m])),*])
      }

      pub fn new(mut f: impl FnMut(&'static str) -> A) -> Self {
        PredefMap([$(f($e)),*])
      }
    }
  };
}

make_predef! {
  SORRY: ":sorry",
}