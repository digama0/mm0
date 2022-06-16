macro_rules! app {
  ($de:expr, {$($e:tt)*}) => { {$($e)*} };
  ($de:expr, ($e:tt + $e2:tt)) => {app!($de, (add $e $e2))};
  ($de:expr, ($e:tt * $e2:tt)) => {app!($de, (mul $e $e2))};
  ($de:expr, [$($e:tt)*]) => { app!($de, $($e)*) };
  ($de:expr, $id:ident[$($e:expr),*]) => {{
    let t = $de.$id;
    let args = &[$($e),*];
    $de.app(t, args)
  }};
  ($de:expr, $e:tt = $e2:tt) => {app!($de, (eq $e $e2))};
  ($de:expr, $e:tt < $e2:tt) => {app!($de, (lt $e $e2))};
  ($de:expr, $e:tt <= $e2:tt) => {app!($de, (le $e $e2))};
  ($de:expr, $e:tt != $e2:tt) => {app!($de, (ne $e $e2))};
  ($de:expr, $e:tt + $e2:tt) => {app!($de, (add $e $e2))};
  ($de:expr, $e:tt * $e2:tt) => {app!($de, (mul $e $e2))};
  ($de:expr, (($id:ident$([$ix:expr])*) $($e:tt)*)) => {app!($de, ($id$([$ix])*) $($e)*)};
  ($de:expr, ($id:ident$([$ix:expr])+) $($e:tt)*) => {
    app!($de, ({$de.$id$([usize::from($ix)])*} $($e)*))
  };
  ($de:expr, ($id:ident $($e:tt)*)) => {app!($de, ({$de.$id} $($e)*))};
  ($de:expr, ({$t:expr} $($e:tt)*)) => {{
    let t = $t;
    let args = &[$(app!($de, $e)),*];
    $de.app(t, args)
  }};
  ($de:expr, $e:ident) => {{$e}};
  ($de:expr, $($e:tt)*) => {{$($e)*}};
}

macro_rules! conv {
  ($de:expr, {$($e:tt)*}) => { {$($e)*} };
  ($de:expr, (UNFOLD $($args:tt)*)) => {conv!($de, UNFOLD $($args)*)};
  ($de:expr, UNFOLD($t:ident $($e:tt)*); $($args:tt)*) => {
    conv!($de, UNFOLD({$de.$id} $($e)*); $($args)*)
  };
  ($de:expr, UNFOLD({$t:expr} $($e:tt)*); $($args:tt)*) => {{
    let t = $t;
    let args = &[$(app!($de, $e)),*];
    let conv = conv!($de, $($args)*);
    $de.unfold(t, args, conv)
  }};
  ($de:expr, (($id:ident$([$ix:expr])*) $($e:tt)*)) => {conv!($de, ($id$([$ix])*) $($e)*)};
  ($de:expr, ($id:ident$([$ix:expr])+) $($e:tt)*) => {{
    let t = $de.$id$([usize::from($ix)])*;
    let args = &[$(conv!($de, $e)),*];
    $de.cong(t, args)
  }};
  ($de:expr, (REFL $($e:tt)*)) => {{
    let e = app!($de, $($e)*);
    $de.refl_conv(e)
  }};
  ($de:expr, SYM $($e:tt)*) => {{
    let conv = conv!($de, $($e)*);
    $de.sym(conv)
  }};
  ($de:expr, ($id:ident $($e:tt)*)) => {{
    let t = $de.$id;
    let args = &[$(conv!($de, $e)),*];
    $de.cong(t, args)
  }};
  ($de:expr, $e:ident) => {{$de.refl_conv($e)}};
  ($de:expr, $($e:tt)*) => {{$($e)*}};
}

macro_rules! thm {
  ($de:expr, {$($e:tt)*}) => { {$($e)*} };
  ($de:expr, ($($e:tt)*) => $($thm:tt)*) => {thm!($de, $($thm)*: $($e)*)};
  ($de:expr, $thm:ident$([$ix:expr])*($($args:expr),*): $($e:tt)*) => {{
    thm!($de, {$de.$thm$([usize::from($ix)])*}($($args),*): $($e)*)
  }};
  ($de:expr, {$thm:expr}($($args:expr),*): $($e:tt)*) => {{
    let th = $thm;
    let args = &[$($args),*];
    let res = app!($de, $($e)*);
    $de.thm(th, args, res)
  }};
  ($de:expr, CONV($th:tt => $($conv:tt)*): $($e:tt)*) => {{
    let th = thm!($de, $th);
    let conv = conv!($de, $($conv)*);
    let res = app!($de, $($e)*);
    $de.conv(res, conv, th)
  }};
  ($de:expr, $thm:ident$([$ix:expr])*($($es:expr),*)($(($($args:tt)*))*): $($e:tt)*) => {{
    let th = $de.$thm$([usize::from($ix)])*;
    let args = &[$($es,)* $(thm!($de, $($args)*),)*];
    let res = app!($de, $($e)*);
    $de.thm(th, args, res)
  }};
}

/// `app_match!(de, e => { arms })` is analogous to `match e { arms }`:
/// it does a pattern match on expression `e`.
/// Each arm has the form `pat => expr,` where `pat` is:
/// * `_` meaning to ignore the value
/// * `x` meaning to capture the value in variable `x`
/// * `(tm pat1 ... patn)` where `tm` is an n-ary term constructor listed in `Predefs`
///
/// The final arm must either be `x/_ => expr` or `!`, where `!` means to throw a
/// "match failed" error if none of the previous arms matched.
///
/// The form `app_match!(de, let pat = e)` does the same thing but acts like
/// `let` instead of `match`: variables in pat are bound in the current block.
macro_rules! app_match {
  // `app_match!(@arms ($de, $sc) $arms)`:
  // Recursive implementation of arm matching, where
  //  $arms ::= $pat => { $rhs } $(,)? $arms
  //         |  $pat => $rhs, $arms
  //         |  <nothing>
  //         |  else $x => $rhs $(,)?
  //         |  @let
  // * $de: the dedup context, $sc: the scrutinee
  // * $pat: the patterns
  // * $rhs: the match result
  (@arms ($de:expr, $sc:expr)) => {
    app_match!(@arms ($de, $sc) else _ => unreachable!("match failed"))
  };
  (@arms ($de:expr, $sc:expr) else $x:pat => $rhs:expr $(,)?) => {{ let $x = $sc; $rhs }};
  (@arms ($de:expr, $sc:expr) $pat:tt => {$($rhs:tt)*}, $($arms:tt)*) => {
    app_match!(@pat ((($de, $sc) {$($rhs)*}) $($arms)*) ($sc,) () () $pat)
  };
  (@arms ($de:expr, $sc:expr) $pat:tt => {$($rhs:tt)*} $($arms:tt)*) => {
    app_match!(@pat ((($de, $sc) {$($rhs)*}) $($arms)*) ($sc,) () () $pat)
  };
  (@arms ($de:expr, $sc:expr) $pat:tt => $rhs:expr, $($arms:tt)*) => {
    app_match!(@pat ((($de, $sc) $rhs) $($arms)*) ($sc,) () () $pat)
  };

  // `app_match!(@pat ((($de, $sc) $rhs) $arms) ($(es,)*) ($vars*) ($stk*) $pat*)`:
  // Implements pattern matching for patterns $pat* against scrutinees $es*.
  // * $de: the dedup context, $sc: the scrutinee
  // * $rhs: the current arm RHS, $arms: the remainder of the arms
  // * $es: the list of expressions to match
  // * $pat: the list of patterns to match against, same length as es
  //     $pat ::= _ | x | ($c $pat*)
  // * $vars: the list of variables that have been bound so far
  // * $stk: the list of matching operations that need to be done (in reverse order)
  //     $stk ::= (let $v = $e) | (match $c ($e) $xs*)
  (@pat $args:tt () ($($vars:ident)*) ($($stk:tt)*)) => {
    app_match!(@build ($args ($($vars)*)) Some(($($vars,)*)), $($stk)*)
  };
  (@pat $args:tt ($e:expr, $($es:tt)*) ($($vars:ident)*) ($($stk:tt)*) _ $($rest:tt)*) => {
    app_match!(@pat $args ($($es)*) ($($vars)*) ($($stk)*) $($rest)*)
  };
  (@pat $args:tt ($e:expr, $($es:tt)*) ($($vars:ident)*) ($($stk:tt)*) $v:ident $($rest:tt)*) => {
    app_match!(@pat $args ($($es)*) ($($vars)* $v) ((let $v = $e) $($stk)*) $($rest)*)
  };
  (@pat $args:tt ($e:expr, $($es:tt)*) $vars:tt $stk:tt ($c:tt $($pats:tt)*) $($rest:tt)*) => {
    app_match!(@gensyms ($args ($($es)*) $vars $stk ($e) $c $($rest)*) () $($pats)*)
  };

  // `app_match!(@gensyms $args ($(($x $pat1))*) $pat2*)`:
  // * $args: arguments used in downstream calls
  //     $args ::= (((($de, $sc) $rhs) $arms) ($(es,)*) ($vars*) ($stk*) ($e) $c $pat*)
  //   * $de, $sc, $rhs, $arms, $es, $pat, $vars, $stk: same as in @pat
  //   * $e: the current expression to match on
  //   * $c: the constant to match against
  // * $x, $pat1: $x is a new gensym to capture the result of $pat1
  // * $pat2: patterns that have not get received gensyms
  (@gensyms $args:tt ($($out:tt)*) $pat:tt $($pats:tt)*) => {
    app_match!(@gensyms $args ($($out)* (_x $pat)) $($pats)*)
  };
  (@gensyms (((($de:expr, $sc:expr) $rhs1:expr) $($arms:tt)*) ($($es:tt)*) $vars:tt
    ($($stk:tt)*) ($e:expr) $c:tt $($rest:tt)*) ($(($x:ident $pats:tt))*)) => {
    app_match!(@pat ((($de, $sc) $rhs1) $($arms)*) ($($de.do_from_usize($x),)* $($es)*) $vars
      ((match $c ($e) $($x)*) $($stk)*) $($pats)* $($rest)*)
  };

  // `app_match!(@build (((($de, $sc) $rhs) $arms) ($vars*)) $out, $stk*)`:
  // Builds the pattern match expression itself in $out.
  // * $de, $sc, $rhs, $arms: the remainder of the arms
  // * $vars: the list of variables that were bound in the pattern
  // * $stk: the list of matching operations that need to be done (in reverse order)
  //     $stk ::= (let $v = $e) | (match $c ($e) $xs*)
  // * $out: an expression of type Option<(...,)> matching operations that need to be done (in reverse order)
  //     $stk ::= (let $v = $e) | (match $c ($e) $xs*)
  (@build ((($args:tt $rhs:expr) @let) ($($vars:ident)*)) $out:expr,) => {
    let ($($vars,)*) = if let Some(x) = $out { x } else { app_match!(@arms $args) };
  };
  (@build ((($args:tt $rhs:expr) $($rest:tt)*) ($($vars:ident)*)) $out:expr,) => {
    if let Some(($($vars,)*)) = $out { $rhs } else { app_match!(@arms $args $($rest)*) }
  };
  (@build $args:tt $out:expr, (let $var:ident = $e:expr) $($stk:tt)*) => {
    app_match!(@build $args { let $var = $e; $out }, $($stk)*)
  };
  (@build (((($de:expr, $sc:expr) $rhs:expr) $($arms:tt)*) ($($vars:ident)*))
    $out:expr, (match $c:ident ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $sc) $rhs) $($arms)*) ($($vars)*))
      if let Some(&[$($x),*]) = $de.is_app_of($e, $de.$c) { $out } else { None },
      $($stk)*)
  };
  (@build (((($de:expr, $sc:expr) $rhs:expr) $($arms:tt)*) ($($vars:ident)*))
    $out:expr, (match ($c:ident $([$ix:expr])*) ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $sc) $rhs) $($arms)*) ($($vars)*))
      if let Some(&[$($x),*]) =
        $de.is_app_of($e, $de.$c$([usize::from($ix)])*) { $out } else { None },
      $($stk)*)
  };
  (@build (((($de:expr, $sc:expr) $rhs:expr) $($arms:tt)*) ($($vars:ident)*))
    $out:expr, (match {$c:expr} ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $sc) $rhs) $($arms)*) ($($vars)*))
      if let Some(&[$($x),*]) = $de.is_app_of($e, $c) { $out } else { None },
      $($stk)*)
  };

  // Entry point. `app_match!($de, $sc => { $arms })`
  ($de:expr, $sc:expr => { $($arms:tt)* }) => {{
    let e = $sc;
    app_match!(@arms ($de, e) $($arms)*)
  }};
  // Entry point. `app_match!($de, let $pat = $sc)` is essentially equivalent to
  // let (xs,) = app_match!($de, $sc => { $pat => (xs,), ! })
  // where xs is the list of pattern variables in $pat.
  ($de:expr, let $pat:tt = $sc:expr) => {
    app_match!(@arms ($de, $sc) $pat => {} @let)
  };
}
