use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::parse_macro_input;

fn impl_enum_tags(
    enum_name: syn::Ident, repr_type: syn::Ident,
    variants: impl Iterator<Item = syn::Variant>,
) -> proc_macro2::TokenStream {
    let mut tag_idents = Vec::new();
    let mut discriminant = 0;

    for variant in variants {
        let tag_ident = format_ident!(
            "{}_TAG",
            variant.ident.to_string().to_ascii_uppercase()
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
            pub const #tag_ident: #repr_type = #discriminant as _;
        });

        discriminant += 1;
    }

    quote! {
        impl #enum_name {
            #(#tag_idents)*
        }
    }
}

/// For now, finds the last `#[repr(...)]` expecting it to be a `u8`.
#[proc_macro_attribute]
pub fn enum_tags(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input_item = parse_macro_input!(input as syn::DeriveInput);
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

    let mut repr_type = None;
    for attr in &input_item.attrs {
        if attr.path().is_ident("repr") {
            let _ = attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("u8") {
                    repr_type = Some(meta.path.get_ident().cloned().unwrap());
                }
                Ok(())
            });
        }
    }

    let Some(repr_type) = repr_type else {
        return syn::Error::new_spanned(
            data_enum.enum_token,
            "Missing #[repr(...)] attribute specifying backing type for discriminant",
        )
        .into_compile_error()
        .into();
    };

    let tags_impl = impl_enum_tags(
        input_item.ident,
        repr_type,
        data_enum.variants.into_iter(),
    );

    quote! {
        #input_item_cloned

        #tags_impl
    }
    .into()
}
