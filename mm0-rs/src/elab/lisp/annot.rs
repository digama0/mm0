//! Annotation for pretty-printing, with an implementation for HTML tags.
use std::fmt::Write;
use crate::elab::lisp::pretty::Pretty;
use crate::util::ArcString;
use crate::elab::environment::{Modifiers};
use pretty::{Doc, RefDoc};

/// Generates an enum from html tags. Used to make annotated pretty printer elements
/// used in doc generation. 
/// The format is `{<enum variant name>, <tag identifier>, (field_name : field_type)*,}
/// There needs to be a trailing comma for the args in the brackets.
macro_rules! html_tag {
  ( $({ $tyname:ident, $id:ident, $($n:ident : $t:ty),* })* ) => {

    #[derive(Debug, Clone)]
    /// Enum for Doc annotations that become HTML tags. All variants have a list
    /// of classes which are (as a string) the first argument to their constructor.
    pub enum HtmlTag {
      $(
        #[allow(missing_docs)]
        $tyname { 
          #[allow(missing_docs)]
          classes: String, 
          $(#[allow(missing_docs)] $n: $t),* }
      ),*
    }
  
    impl HtmlTag {
      /// Makes a constructor for each html tag. example:
      /// fn a(classes: String, href: String) -> Self {
      ///   Self::A { classes, href }
      ///}
      $(
        #[allow(missing_docs)]
        pub fn $id(classes: String, $($n: $t),*) -> Self {
          Self::$tyname {
            classes,
            $($n),*
          }
        }
      )*
  
      /// Makes an open tag for each enum variant. Example for HtmlTag::A { classes, href }:
      /// <a classes="contents_of_class_field" href="content_of_href_field">
      pub fn open(&self) -> String {
        match self {
          $(
            Self::$tyname { classes, $($n),* } => {
              let mut s = if classes.is_empty() {
                format!(
                  "<{}",
                  stringify!($id),
                )
              } else {
                format!(
                  "<{} class=\"{}\"",
                  stringify!($id),
                  classes,
                )
              };
              $(
                s.push(' ');
                s.push_str(concat!(stringify!($n), "=\""));
                s += format!("{}", $n).as_str();
                s.push_str("\"");
              )*
              s.push('>');
              s
            }
          ),*
        }
      }
          
      /// Makes a close tag for each enum variant. Example for HtmlTag::A { classes, href }:
      /// </a>
      pub fn close(&self) -> &'static str {
        match self {
          $(
            Self::$tyname {..} => concat!(concat!("</", stringify!($id)), ">")
          ),*
        }
      }
    }
  }
}    
    
// Make the desired HTML tags as variants of an enum.
// As an example, the a/anchor tag gets the following enum variant, a constructor
// invoked as `HtmlTag::a(classes: String, href: String)`, and functions producing
// the open/close tags.
// ```
// HtmlTag::A {
//   classes: String,
//   href: String
// }
// ```
html_tag!(
    { A, a, href: String }
    { Pre, pre, }
    { Body, body, }
    { Div, div, }
);
   
/// Trait implemented for types that can be inserted as annotations in
/// pretty printer docs. The structure is loosely based on the `Visit` traits in `syn`.
/// The functions in `..lisp::pretty` call these on the elements they're 
/// assembling/printing in all cases, but the trait methods will only add something 
/// if the annotation type calls for it. The default implementation for each trait 
/// method just returns the underlying components as a doc with nothing added.
///
/// The basic problem is that you can't (easily) pretty-print the 
/// item, THEN annotate it, since the annotations might require information that's more 
/// difficult to recover from the string representation. If, for example, you need the name of 
/// some identifier in order to produce an intra-doc link, it's easier to make that annotation 
/// while you still have it as an `AtomID` that you already know is the right thing.
/// See `..pretty::Pretty::pp_sort` for an example of how this might look.
pub trait IsAnnotation: Clone {
  /// Add annotations to a sort name.
  fn ann_sort_name<'a>(p: &'a Pretty<'a, Self>, name: &ArcString) -> RefDoc<'a, Self> {
    p.alloc(Doc::text(name.to_string()))
  }

  /// Add annotations to sort modifiers.
  fn ann_sort_mods<'a>(p: &'a Pretty<'a, Self>, mods: &Modifiers) -> RefDoc<'a, Self> {
    p.alloc(Doc::text(mods.to_string()))
  }

}

/// Uses the default implementations, which do nothing.
impl IsAnnotation for () {}

impl IsAnnotation for HtmlTag {
  /// Example: `<pre class="sortname">wff</pre>`
  fn ann_sort_name<'a>(p: &'a Pretty<'a, Self>, name: &ArcString) -> RefDoc<'a, Self> {
    p.alloc(Doc::Annotated(
      HtmlTag::Pre { classes: "sortname".to_string() }, 
      p.alloc(Doc::text(name.to_string()))
    ))
  }

  /// Example: `<pre class="sortmod">pure strict</pre>`
  fn ann_sort_mods<'a>(p: &'a Pretty<'a, Self>, mods: &Modifiers) -> RefDoc<'a, Self> {
    p.alloc(Doc::Annotated(
      HtmlTag::Pre { classes: "sortmod".to_string() },
      p.alloc(Doc::text(mods.to_string()))
    ))
  }
}

/// implements `RenderAnnotated`. Is currently specialized to HtmlTag.
#[derive(Debug, Clone)]
pub struct AnnotPrinter<W: Write> {
  writer: W,
  stack: Vec<&'static str>
}

impl<W: Write> AnnotPrinter<W> {
  /// Make a new `AnnotPrinter` from some writer. 
  pub fn new(writer: W) -> Self {
    AnnotPrinter { writer, stack: Vec::new() }
  }

  /// Eliminate the `AnnotPrinter` taking back the inner writer.
  pub fn into_inner(self) -> W {
    self.writer
  }
}

impl<W: Write> Write for AnnotPrinter<W> {
  fn write_str(&mut self, s : &str) -> std::fmt::Result {
    self.writer.write_str(s)
  }
}

impl<'a, W: Write> pretty::Render for AnnotPrinter<W>
{
    type Error = std::fmt::Error;

    fn write_str(&mut self, s: &str) -> std::result::Result<usize, Self::Error> {
        self.write_str_all(s).map(|_| s.len())
    }

    fn write_str_all(&mut self, s: &str) -> std::result::Result<(), Self::Error> {
        self.writer.write_str(s)
    }

    fn fail_doc(&self) -> Self::Error {
      std::fmt::Error::default()
    }
}

impl<'a, W: Write> pretty::RenderAnnotated<'a, HtmlTag> for AnnotPrinter<W> {
  /// Push the close annotation's close tag to the stack for later
  /// and write the open tag representation to the underlying writer
  fn push_annotation(&mut self, annotation: &'a HtmlTag) -> Result<(), Self::Error> {
    self.stack.push(annotation.close());
    self.writer.write_str(annotation.open().as_str())
  }
  
  /// Used when this annotation's scope closes, so we just pop the close 
  /// tag off the stack and write it to the underlying writer
  fn pop_annotation(&mut self) -> Result<(), Self::Error> {
    if let Some(x) = self.stack.pop() {
      self.writer.write_str(x)
    } else {
      Ok(())
    }
  }
}

#[cfg(test)]
mod annot_tests {
  use super::*;

  #[test]
  fn annot_test1() {
    let sortname = ArcString::from("wff".to_string());
    let env = crate::elab::environment::Environment::new();
    let source = crate::lined_string::LinedString::from("asdf".to_string());
    let fe = crate::elab::lisp::print::FormatEnv { source: &source, env: &env };
    let mut writer = String::new();
    let mut ap = AnnotPrinter::new(&mut writer);

    // uses `ap` to write to `writer`. You need to create a `writer`
    // struct as a separate type (a) because the pretty crate demands 
    // that you implement the RenderAnnotated trait for something, and (b)
    // because you need some sort of structure to keep track of nested annotations
    // if you're going to do something that needs to surround, like html tags.
    fe.pretty_annotated(|p| {
      let doc = <HtmlTag as IsAnnotation>::ann_sort_name(p, &sortname);
      p.alloc(Doc::Annotated(HtmlTag::div(String::new()), doc))
      .render_raw(80, &mut ap)
      .expect("Bad write");
    });
    assert_eq!(
      writer.as_str(),
      "<div><pre class=\"sortname\">wff</pre></div>"
    );

  }
  #[test]
  fn annot_test2() {
    let env = crate::elab::environment::Environment::new();
    let source = crate::lined_string::LinedString::from("asdf".to_string());
    let fe = crate::elab::lisp::print::FormatEnv { source: &source, env: &env };
    let mut writer = String::new();
    let mut ap = AnnotPrinter::new(&mut writer);

    fe.pretty_annotated(|p| {
      let mut doc = p.alloc(Doc::text("linked_item"));
      doc = p.alloc(Doc::Annotated(
        HtmlTag::a(format!("some_class"), format!("place.html")),
        doc
      ));
      doc.render_raw(80, &mut ap).expect("Bad write");
    });
    assert_eq!(
      writer.as_str(),
      "<a class=\"some_class\" href=\"place.html\">linked_item</a>"
    );

  }

}
