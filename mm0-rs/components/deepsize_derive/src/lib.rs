//! A basic DeepSizeOf Derive implementation
//!
//! Mainly from `syn`'s heap_size derive example:
//! <https://github.com/dtolnay/syn/commits/master/examples/heapsize/heapsize_derive/src/lib.rs>

extern crate proc_macro;

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{
    parse_macro_input, parse_quote, Data, DeriveInput, Fields, GenericParam, Generics, Index,
};

#[proc_macro_derive(DeepSizeOf)]
pub fn derive_deep_size(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    if !cfg!(feature = "nodummy") {
        return proc_macro::TokenStream::new();
    }

    // Parse the input tokens into a syntax tree.
    let input = parse_macro_input!(input as DeriveInput);

    // Used in the quasi-quotation below as `#name`.
    let name = input.ident;

    // Add a bound `T: DeepSizeOf` to every type parameter T.
    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    // Generate an expression to sum up the size of each field.
    let sum = deepsize_sum(&input.data, &name);

    let expanded = quote! {
        // The generated impl.
        impl #impl_generics crate::deepsize::DeepSizeOf for #name #ty_generics #where_clause {
            fn deep_size_of_children(&self, context: &mut crate::deepsize::Context) -> usize {
                #sum
            }
        }
    };

    // Hand the output tokens back to the compiler.
    proc_macro::TokenStream::from(expanded)
}

// Add a bound `T: DeepSizeOf` to every type parameter T.
fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(crate::deepsize::DeepSizeOf));
        }
    }
    generics
}

fn match_fields(fields: &syn::Fields) -> TokenStream {
    match fields {
        Fields::Named(ref fields) => {
            let recurse = fields.named.iter().map(|f| {
                let name = &f.ident;
                quote_spanned! {f.span()=>
                    crate::deepsize::DeepSizeOf::deep_size_of_children(&self.#name, context)
                }
            });
            quote! {
                0 #(+ #recurse)*
            }
        }
        Fields::Unnamed(ref fields) => {
            let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                let index = Index::from(i);
                quote_spanned! {f.span()=>
                    crate::deepsize::DeepSizeOf::deep_size_of_children(&self.#index, context)
                }
            });
            quote! {
                0 #(+ #recurse)*
            }
        }
        Fields::Unit => {
            // Unit structs cannot own more than 0 bytes of memory.
            quote!(0)
        }
    }
}

fn match_enum_fields(fields: &syn::Fields) -> TokenStream {
    match fields {
        Fields::Named(ref fields) => {
            let recurse = fields.named.iter().map(|f| {
                let name = &f.ident;
                quote_spanned! {f.span()=>
                    crate::deepsize::DeepSizeOf::deep_size_of_children(#name, context)
                }
            });
            quote! {
                0 #(+ #recurse)*
            }
        }
        Fields::Unnamed(ref fields) => {
            let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                let i = syn::Ident::new(&format!("_{}", i), proc_macro2::Span::call_site());
                quote_spanned! {f.span()=>
                    crate::deepsize::DeepSizeOf::deep_size_of_children(#i, context)
                }
            });
            quote! {
                0 #(+ #recurse)*
            }
        }
        Fields::Unit => {
            // Unit structs cannot own more than 0 bytes of memory.
            quote!(0)
        }
    }
}

fn get_matcher(var: &syn::Variant) -> TokenStream {
    let matcher = match &var.fields {
        Fields::Unit => TokenStream::new(),
        Fields::Unnamed(fields) => {
            let fields: TokenStream = (0..fields.unnamed.len())
                .map(|n| {
                    let i = syn::Ident::new(&format!("_{}", n), proc_macro2::Span::call_site());
                    quote!(#i,)
                })
                .collect();
            quote!((#fields))
        }
        Fields::Named(fields) => {
            let fields: TokenStream = fields
                .named
                .iter()
                .map(|f| {
                    let i = f.ident.as_ref().unwrap();
                    quote!(#i,)
                })
                .collect();
            quote!({#fields})
        }
    };

    quote!(#matcher)
}

/// Generate an expression to sum up the size of each field.
fn deepsize_sum(data: &Data, struct_name: &proc_macro2::Ident) -> TokenStream {
    match *data {
        Data::Struct(ref inner) => {
            match_fields(&inner.fields)
        }
        Data::Enum(ref inner) => {
            let arms = inner.variants.iter()
                .map(|var| {
                    let matcher = get_matcher(var);
                    let output = match_enum_fields(&var.fields);
                    let name = &var.ident;
                    let ident = quote!(#struct_name::#name);
                    quote!(#ident #matcher => #output,)
                });

            quote! {
                match self {
                    #(#arms)*
                    _ => 0 // This is needed for empty enums
                }
            }
        }
        Data::Union(_) => unimplemented!(),
    }
}
