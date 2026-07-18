//! Derives for the `mmcc` binary encoding (see `mmcc::encode`).
//!
//! The generated code is the field-by-field walk and nothing else. Everything shared
//! across types — the context structs, which types are interned — is declared by the
//! `interned!` macro in `mmcc::encode`, because a derive sees one type at a time and
//! emits its tokens before the next runs, so it can never be the one to declare an
//! object that every type contributes to.
//!
//! A struct writes its fields back to back, in declaration order; nothing marks where one
//! ends, since the reader knows the shape. An enum writes a `uleb` variant tag first, so
//! adding a variant at the end is compatible and inserting one in the middle is not.

extern crate proc_macro;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, parse_quote, Data, DeriveInput, Fields, GenericParam, Generics};

/// Derive `Encode`: write every field in declaration order, after a variant tag for an
/// enum.
#[proc_macro_derive(Encode)]
pub fn derive_encode(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
  let input = parse_macro_input!(input as DeriveInput);
  let name = &input.ident;
  let generics = add_bound(input.generics.clone(), parse_quote!(::mmcc::encode::Encode));
  let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
  let body = encode_body(&input.data, name);
  quote! {
    impl #impl_generics ::mmcc::encode::Encode for #name #ty_generics #where_clause {
      fn encode(&self, ctx: &mut ::mmcc::encode::EncodeCtx, out: &mut ::std::vec::Vec<u8>) {
        #body
      }
    }
  }.into()
}

/// Derive `Decode`, the exact inverse of [`derive_encode`].
#[proc_macro_derive(Decode)]
pub fn derive_decode(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
  let input = parse_macro_input!(input as DeriveInput);
  let name = &input.ident;
  let generics = add_bound(input.generics.clone(), parse_quote!(::mmcc::encode::Decode));
  let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
  let body = decode_body(&input.data, name);
  quote! {
    impl #impl_generics ::mmcc::encode::Decode for #name #ty_generics #where_clause {
      fn decode(
        ctx: &mut ::mmcc::encode::DecodeCtx, buf: &mut &[u8]
      ) -> ::mmcc::encode::Result<Self> {
        #body
      }
    }
  }.into()
}

/// Bound every type parameter by the trait being derived.
fn add_bound(mut generics: Generics, bound: syn::TypeParamBound) -> Generics {
  for param in &mut generics.params {
    if let GenericParam::Type(ty) = param { ty.bounds.push(bound.clone()) }
  }
  generics
}

/// Bindings for a variant's fields, named positionally.
///
/// Never the field's own name: a field called `ctx`, `buf` or `out` would shadow the
/// parameters the generated body threads through, and the code would either fail to
/// compile or pass the wrong value along.
fn binders(fields: &Fields) -> Vec<syn::Ident> {
  (0..fields.len()).map(|i| format_ident!("__f{}", i)).collect()
}

/// The pattern that binds a variant's fields, e.g. `{ a: __f0 }` or `(__f0, __f1)`.
fn pattern(fields: &Fields, bs: &[syn::Ident]) -> TokenStream {
  match fields {
    Fields::Named(f) => {
      let names = f.named.iter().map(|f| f.ident.as_ref().expect("a named field has a name"));
      quote!({ #(#names: #bs),* })
    }
    Fields::Unnamed(_) => quote!(( #(#bs),* )),
    Fields::Unit => quote!(),
  }
}

/// Rebuild a value from bindings already decoded.
fn construct(path: TokenStream, fields: &Fields, bs: &[syn::Ident]) -> TokenStream {
  match fields {
    Fields::Named(f) => {
      let names = f.named.iter().map(|f| f.ident.as_ref().expect("a named field has a name"));
      quote!(#path { #(#names: #bs),* })
    }
    Fields::Unnamed(_) => quote!(#path( #(#bs),* )),
    Fields::Unit => quote!(#path),
  }
}

fn encode_body(data: &Data, name: &syn::Ident) -> TokenStream {
  match data {
    Data::Struct(s) => {
      let bs = binders(&s.fields);
      let pat = pattern(&s.fields, &bs);
      // Bind through the pattern rather than by index, so a named and a tuple struct
      // take the same path and field order is read off the declaration either way.
      quote! {
        let #name #pat = self;
        #(::mmcc::encode::Encode::encode(#bs, ctx, out);)*
      }
    }
    Data::Enum(e) if e.variants.is_empty() =>
      // An uninhabited enum has no value to write. The match has to go through the place
      // `*self`, not `self`: a `&E` is inhabited whatever `E` is, so matching it needs an arm.
      quote!(match *self {}),
    Data::Enum(e) => {
      let arms = e.variants.iter().enumerate().map(|(i, v)| {
        let vname = &v.ident;
        let bs = binders(&v.fields);
        let pat = pattern(&v.fields, &bs);
        let tag = i as u64;
        quote! {
          #name::#vname #pat => {
            ::mmcc::encode::uleb(#tag, out);
            #(::mmcc::encode::Encode::encode(#bs, ctx, out);)*
          }
        }
      });
      quote!(match self { #(#arms)* })
    }
    Data::Union(_) => quote!(compile_error!("Encode cannot be derived for a union")),
  }
}

fn decode_body(data: &Data, name: &syn::Ident) -> TokenStream {
  match data {
    Data::Struct(s) => {
      let bs = binders(&s.fields);
      let build = construct(quote!(#name), &s.fields, &bs);
      quote! {
        #(let #bs = ::mmcc::encode::Decode::decode(ctx, buf)?;)*
        Ok(#build)
      }
    }
    Data::Enum(e) => {
      let arms = e.variants.iter().enumerate().map(|(i, v)| {
        let vname = &v.ident;
        let bs = binders(&v.fields);
        let build = construct(quote!(#name::#vname), &v.fields, &bs);
        let tag = i as u64;
        quote! {
          #tag => {
            #(let #bs = ::mmcc::encode::Decode::decode(ctx, buf)?;)*
            Ok(#build)
          }
        }
      });
      quote! {
        match ::mmcc::encode::read_uleb(buf)? {
          #(#arms)*
          _ => ::std::result::Result::Err(
            ::mmcc::encode::DecodeErr("unknown variant tag")),
        }
      }
    }
    Data::Union(_) => quote!(compile_error!("Decode cannot be derived for a union")),
  }
}
