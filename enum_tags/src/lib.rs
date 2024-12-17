use std::fmt;

use proc_macro::TokenStream;
use quote::quote;

enum Visibility {
    Public(proc_macro2::Span),
    Private,
}

impl fmt::Display for Visibility {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Public(..) => "public",
            Self::Private => "private",
        }
        .fmt(f)
    }
}

impl syn::parse::Parse for Visibility {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let identifier = input.parse::<syn::Ident>()?;
        match identifier.to_string().as_str() {
            "public" => Ok(Self::Public(identifier.span())),
            "private" => Ok(Self::Private),
            _ => Err(syn::Error::new_spanned(
                identifier,
                "Unexpected visibility: expected `public` or `private`",
            )),
        }
    }
}

struct EnumTagsArgs {
    visibility: Visibility,
    repr_type: syn::Type,
}

impl syn::parse::Parse for EnumTagsArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        mod kw {
            use syn::custom_keyword;

            custom_keyword!(repr);
        }

        let visibility = input.parse()?;

        input.parse::<syn::Token![,]>().map_err(|mut error| {
            error.combine(syn::Error::new(
                input.span(),
                format!("Missing comma after `{}` visibility", visibility),
            ));
            error
        })?;

        input.parse::<kw::repr>().map_err(|mut error| {
            error.combine(syn::Error::new(
                input.span(),
                format!("Missing `repr` after `{},`", visibility),
            ));
            error
        })?;

        let content;
        syn::parenthesized!(content in input);
        let repr_type = content.parse()?;

        Ok(Self {
            visibility,
            repr_type,
        })
    }
}

// TODO: make this somehow a trait implementation.
fn impl_enum_tags(
    enum_visibility: syn::Visibility,
    enum_name: syn::Ident,
    repr_type: syn::Type,
    variants: impl Iterator<Item = syn::Variant>,
) -> proc_macro2::TokenStream {
    let mut tag_idents = vec![];
    let mut match_cases = vec![];
    let mut discriminant = 0;

    for variant in variants {
        let variant_name = variant.ident;
        let tag_ident = quote::format_ident!(
            "{}_TAG",
            variant_name.to_string().to_ascii_uppercase()
        );

        if let Some((_, custom_discriminant)) = variant.discriminant {
            match custom_discriminant {
                syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Int(int_literal),
                    ..
                }) => match int_literal.base10_parse::<usize>() {
                    Ok(int_literal) => discriminant = int_literal,
                    Err(error) => {
                        return error.into_compile_error();
                    }
                },
                other => {
                    return syn::Error::new_spanned(
                        other,
                        "Only literal discriminants are allowed",
                    )
                    .into_compile_error();
                }
            }
        }

        tag_idents.push(quote! {
            #[doc = concat!("`#[enum_tags]`-generated tag for the variant `Self::", stringify!(#variant_name), "`.")]
            #enum_visibility const #tag_ident: #repr_type = #discriminant as _;
        });

        match variant.fields {
            syn::Fields::Named(_) => {
                match_cases.push(quote! {
                    Self::#variant_name { .. } => #discriminant as _
                });
            }
            syn::Fields::Unnamed(_) => {
                match_cases.push(quote! {
                    Self::#variant_name(..) => #discriminant as _
                });
            }
            syn::Fields::Unit => {
                match_cases.push(quote! {
                    Self::#variant_name => #discriminant as _
                });
            }
        }

        discriminant += 1;
    }

    quote! {
        impl #enum_name {
            #(#tag_idents)*

            #[doc = "`#[enum_tags]`-generated getter for this variant's tag."]
            #enum_visibility const fn tag(&self) -> #repr_type {
                match self {
                    #(#match_cases),*
                }
            }
        }
    }
}

/// Constructs an `impl` for the given `enum` with constants for the
/// discriminant value of each variant.
///
/// Usage examples:
///
/// * `#[enum_tags(public, repr(u8))]`
/// * `#[enum_tags(private, repr(u32))]`
///
/// Note that the `repr` type can be any numerical type to which a `usize` can
/// be casted to implicitly with the `as` keyword --- it is not the same as the
/// type for which you may `#[repr(...)]` the `enum`.
#[proc_macro_attribute]
pub fn enum_tags(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = syn::parse_macro_input!(args as EnumTagsArgs);

    let input_item = syn::parse_macro_input!(input as syn::DeriveInput);
    let input_item_cloned = input_item.clone();

    let data_enum = match input_item.data {
        syn::Data::Enum(data_enum) => data_enum,
        syn::Data::Struct(syn::DataStruct {
            struct_token: syn::token::Struct { span },
            ..
        })
        | syn::Data::Union(syn::DataUnion {
            union_token: syn::token::Union { span },
            ..
        }) => {
            return syn::Error::new(span, "Item must be an `enum`")
                .into_compile_error()
                .into();
        }
    };

    let visibility = match args.visibility {
        Visibility::Public(span) => {
            syn::Visibility::Public(syn::token::Pub { span })
        }
        Visibility::Private => syn::Visibility::Inherited,
    };

    let tags_impl = impl_enum_tags(
        visibility,
        input_item.ident,
        args.repr_type,
        data_enum.variants.into_iter(),
    );

    quote! {
        #input_item_cloned

        #tags_impl
    }
    .into()
}
