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
  ($de:expr, CACHE[$thm:ident$([$ix:expr])*]: $($e:tt)*) => {{
    let th = $de.$thm$([usize::from($ix)])*;
    $de.cache(th, |de| app!(de, $($e)*))
  }};
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

macro_rules! app_match {
  (@build ((($args:tt $rhs1:expr) $($rest:tt)+) ($($vars:ident)*)) $out:expr,) => {
    if let Some(($($vars,)*)) = $out { $rhs1 } else {
      app_match!(@arms $args $($rest)+)
    }
  };
  (@build $args:tt $out:expr, (let $var:ident = $e:expr) $($stk:tt)*) => {
    app_match!(@build $args { let $var = $e; $out }, $($stk)*)
  };
  (@build (((($de:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($vars:ident)*))
    $out:expr, (match $c:ident ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $e1) $rhs1) $($rest1)+) ($($vars)*))
      if let Some(&[$($x),*]) = $de.is_app_of($e, $de.$c) { $out } else { None },
      $($stk)*)
  };
  (@build (((($de:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($vars:ident)*))
    $out:expr, (match ($c:ident $([$ix:expr])*) ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $e1) $rhs1) $($rest1)+) ($($vars)*))
      if let Some(&[$($x),*]) =
        $de.is_app_of($e, $de.$c$([usize::from($ix)])*) { $out } else { None },
      $($stk)*)
  };
  (@build (((($de:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($vars:ident)*))
    $out:expr, (match {$c:expr} ($e:expr) $($x:ident)*) $($stk:tt)*) => {
    app_match!(@build (((($de, $e1) $rhs1) $($rest1)+) ($($vars)*))
      if let Some(&[$($x),*]) = $de.is_app_of($e, $c) { $out } else { None },
      $($stk)*)
  };
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
  (@gensyms $args:tt ($($out:tt)*) $pat:tt $($pats:tt)*) => {
    app_match!(@gensyms $args ($($out)* (x $pat)) $($pats)*)
  };
  (@gensyms (((($de:expr, $e1:expr) $rhs1:expr) $($rest1:tt)+) ($($es:tt)*) $vars:tt
    ($($stk:tt)*) ($e:expr) $c:tt $($rest:tt)*) ($(($x:ident $pats:tt))*)) => {
    app_match!(@pat ((($de, $e1) $rhs1) $($rest1)+) ($($de.do_from_usize($x),)* $($es)*) $vars
      ((match $c ($e) $($x)*) $($stk)*) $($pats)* $($rest)*)
  };
  (@arms ($de:expr, $e:expr) $pat1:tt => {$($rhs1:tt)*}, $($rest:tt)+) => {
    app_match!(@pat ((($de, $e) {$($rhs1)*}) $($rest)+) ($e,) () () $pat1)
  };
  (@arms ($de:expr, $e:expr) $pat1:tt => {$($rhs1:tt)*} $($rest:tt)+) => {
    app_match!(@pat ((($de, $e) {$($rhs1)*}) $($rest)+) ($e,) () () $pat1)
  };
  (@arms ($de:expr, $e:expr) $pat1:tt => $rhs1:expr, $($rest:tt)+) => {
    app_match!(@pat ((($de, $e) $rhs1) $($rest)+) ($e,) () () $pat1)
  };
  (@arms ($de:expr, $e:expr) $x:pat => $rhs:expr $(,)?) => {{ let $x = $e; $rhs }};
  (@arms ($de:expr, $e:expr) !) => {
    app_match!(@arms ($de, $e) _ => unreachable!("match failed"))
  };
  ($de:expr, $e:expr => { $($args:tt)* }) => {{
    let e = $e;
    app_match!(@arms ($de, e) $($args)*)
  }};
}

pub(crate) use {app, thm, conv, app_match};
