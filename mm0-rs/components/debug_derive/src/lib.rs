use proc_macro::TokenStream;
use quote::{
    format_ident,
    quote
};
use syn::{
    parse_quote,
    parse_macro_input,
    Ident,
    Fields,
    Data,
    punctuated::Punctuated,
    token::Comma,
};


// Make a single match arm for either a struct or single enum variant.
// as an example, for the mm0-rs type `Sort`, this function produces:
//
// ```
// Sort { atom, name, span, full, mods } => {
//     let mut base = f.debug_struct("Sort");
//     base.field("atom", format_args!("{:#?}", fe.to(atom))
//     base.field("name", format_args!("{:#?}", fe.to(name))
//     base.field("span", format_args!("{:#?}", fe.to(span))
//     base.field("full", format_args!("{:#?}", fe.to(full))
//     base.field("mods", format_args!("{:#?}", fe.to(mods))
//     base.finish()
// }
// ```
fn mk_arm(
    item_ident: &Ident,
    fields: &Fields,
    variant_ident: Option<&Ident>
) -> syn::Arm {
    let (item_path, namestring): (syn::Path, String) = match variant_ident {
        // if struct
        None => (
            parse_quote!(#item_ident),
            format!("{item_ident}")
        ),
        // if enum
        Some(variant) => (
            parse_quote!(#item_ident::#variant),
            format!("{item_ident}::{variant}")
        )
    };

    match fields {
        Fields::Named(named) => {
            // the names of fields as idents (iterator).
            let all_idents = named.named.iter().map(|field| field.ident.as_ref().expect(
                "All fields in a Field::Named should have names"
            ));
            let all_idents_copy = all_idents.clone();

            parse_quote! {
                #item_path { #(#all_idents),* } => {
                    let mut base = f.debug_struct(#namestring);
                    #(
                        base.field(
                            stringify!(#all_idents_copy),
                            &format_args!("{:#?}", fe.to(#all_idents_copy))
                        );
                    )*
                    base.finish()
                }
            }
        },
        Fields::Unnamed(unnamed) => {
            let field_idents = unnamed.unnamed.iter().enumerate().map(|(idx, _)| format_ident!("__{}", idx));
            let field_idents_copy = field_idents.clone();

            parse_quote! {
                #item_path (#(#field_idents),*) => {
                    let mut base = f.debug_tuple(#namestring);
                    #(
                        base.field(&format_args!("{:#?}", fe.to(#field_idents_copy)));
                    )*
                    base.finish()
                }
            }
        }
        Fields::Unit => {
            parse_quote! {
                #item_path => {
                    let mut base = f.debug_struct(#namestring);
                    base.finish()
                }
            }
        }
    }
}

// Same as mk_arm, but only tries to match on/print public fields
#[allow(unused)]
fn mk_arm_pub(
    item_ident: &Ident,
    fields: &Fields,
    variant_ident: Option<&Ident>
) -> syn::Arm {
    let (item_path, namestring): (syn::Path, String)  = match variant_ident {
        // if struct
        None => (
            parse_quote!(#item_ident),
            format!("{item_ident}")
        ),
        // if enum
        Some(variant) => (
            parse_quote!(#item_ident::#variant),
            format!("{item_ident}::{variant}")
        )
    };

    match fields {
        Fields::Named(named) => {
            let mut pub_pats = named.named.iter().filter_map(|field| {
                match field.vis {
                    syn::Visibility::Inherited => None,
                    _ => {
                        let f = field.ident.as_ref().unwrap();
                        let as_pat: syn::Pat = parse_quote!(#f);
                        Some(as_pat)
                    }
                }
            }).collect::<Punctuated<syn::Pat, Comma>>();
            pub_pats.push(parse_quote! { .. });

            let pub_idents = named.named.iter().filter_map(|field| {
                match field.vis {
                    syn::Visibility::Inherited => None,
                    _ => Some(field.ident.as_ref().unwrap()),
                }
            });

            parse_quote! {
                #item_path { #pub_pats } => {
                    let mut base = f.debug_struct(#namestring);
                    #(
                        base.field(
                            stringify!(#pub_idents),
                            &format_args!("{:#?}", fe.to(#pub_idents))
                        );
                    )*
                    base.finish()
                }
            }
        },
        Fields::Unnamed(unnamed) => {
            let underscore = format_ident!("_");
            let match_idents = unnamed.unnamed.iter().enumerate().map(|(idx, field)| {
                match field.vis {
                    syn::Visibility::Inherited => underscore.clone(),
                    _ => format_ident!("__{}", idx)
                }
            });

            let pub_idents = match_idents.clone().filter(|id| id != &underscore);
            parse_quote! {
                #item_path (#(#match_idents),*) => {
                    let mut base = f.debug_tuple(#namestring);
                    #(
                        base.field(&format_args!("{:#?}", fe.to(#pub_idents)));
                    )*
                    base.finish()
                }
            }
        },
        Fields::Unit => {
            parse_quote! {
                #item_path => {
                    let mut base = f.debug_struct(#namestring);
                    base.finish()
                }
            }
        },
    }
}

// Generates the actual token tree.
fn mk_item(derive_input: &mut syn::DeriveInput, pub_only: bool) -> syn::ItemImpl {
    let format_env_path: syn::Path = parse_quote!(crate::elab::lisp::print::FormatEnv);
    let env_debug_path: syn::Path = parse_quote!(crate::elab::lisp::debug::EnvDebug);

    // For items with type parameters, add a trait bound of `EnvDebug`.
    // As of right now, deriving EnvDebug for some type T requires that all of its type parameters
    // also implement EnvDebug.
    for param in &mut derive_input.generics.params {
        match param {
            syn::GenericParam::Type(type_param) => {
                let bound: syn::TypeParamBound = parse_quote!(EnvDebug);
                type_param.bounds.push(bound);
            },
            _ => continue
        }
    }

    let (ident, data) = (&derive_input.ident, &derive_input.data);
    let (impl_generics, type_generics, where_clause) = &derive_input.generics.split_for_impl();

    match data {
        Data::Struct(inner) => {
            let fields = if pub_only {
                mk_arm_pub(ident, &inner.fields, None)
            } else {
                mk_arm(ident, &inner.fields, None)
            };
            parse_quote! {
                impl #impl_generics #env_debug_path for #ident #type_generics #where_clause {
                    fn env_dbg<'__a>(&self, fe: #format_env_path<'__a>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                      match self {
                          #fields
                      }
                    }
                }
            }
        },
        Data::Enum(inner) => {
            let arms: Punctuated<syn::Arm, Comma> = if pub_only {
                inner.variants.iter().map(|variant| mk_arm_pub(ident, &variant.fields, Some(&variant.ident))).collect()
            } else {
                inner.variants.iter().map(|variant| mk_arm(ident, &variant.fields, Some(&variant.ident))).collect()
            };
            parse_quote! {
                impl #impl_generics #env_debug_path for #ident #type_generics #where_clause {
                    fn env_dbg<'__a>(&self, fe: #format_env_path<'__a>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        match self {
                            #arms
                        }
                    }
                }
            }
        },
        Data::Union(..) => panic!("derive handler for EnvDebug cannot handle union items (only structs and enums)")
    }
}

/// Use this one if you only want print all the fields (both public and private) of an item.
#[proc_macro_derive(EnvDebug)]
pub fn derive_env_debug(input: TokenStream) -> TokenStream {
    let mut parsed = parse_macro_input!(input as syn::DeriveInput);
    let tt = mk_item(&mut parsed, false);

    TokenStream::from(quote! {
        #tt
    })
}

/// Use this one if you only want to print the public fields of an item.
#[proc_macro_derive(EnvDebugPub)]
pub fn derive_env_debug_pub(input: TokenStream) -> TokenStream {
    let mut parsed = parse_macro_input!(input as syn::DeriveInput);
    let tt = mk_item(&mut parsed, true);

    TokenStream::from(quote! {
        #tt
    })
}
