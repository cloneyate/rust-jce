use proc_macro::TokenStream;
use proc_macro2::TokenTree;
use quote::quote;
use std::error::Error;
use syn::{Data, DeriveInput};

macro_rules! error {
    ($e:expr) => {
        return Err($e.into())
    };
}

#[proc_macro_derive(JceStruct, attributes(jce))]
pub fn jce_struct(input: TokenStream) -> TokenStream {
    try_jce_struct(input).unwrap()
}

#[proc_macro_derive(JceEnum, attributes(jce))]
pub fn jce_enum(input: TokenStream) -> TokenStream {
    try_jce_enum(input).unwrap()
}

fn try_jce_struct(input: TokenStream) -> Result<TokenStream, Box<dyn Error>> {
    let input: DeriveInput = syn::parse(input)?;

    let s = match input.data {
        Data::Struct(s) => s,
        _ => error!("JceStruct can only derive for struct"),
    };

    let (imp_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let name = input.ident;

    let default = quote! { ::core::default::Default::default() };
    let mut fields_default: Vec<proc_macro2::TokenStream> = vec![];

    let mut fields_encoded_len: Vec<proc_macro2::TokenStream> = vec![];

    let mut tags: Vec<u8> = vec![];

    let mut tag: i32 = -1;
    for field in &s.fields {
        let ident = &field.ident;
        fields_default.push(quote!(#ident: #default));

        fields_encoded_len.push(quote!(::jce::types::JceType::write_len(&self.#ident)));

        if field.attrs.is_empty() {
            tag += 1;
            tags.push(tag as u8);
            continue;
        }

        for attr in &field.attrs {
            if attr
                .path
                .segments
                .iter()
                .find(|seg| seg.ident == "jce")
                .is_some()
            {
                if let Some(tt) = attr.tokens.clone().into_iter().next() {
                    match tt {
                        TokenTree::Group(e) => {
                            let mut stream = e.stream().into_iter();

                            match (stream.next(), stream.next()) {
                                (Some(TokenTree::Ident(ident)), Some(TokenTree::Punct(punct))) => {
                                    if ident != "tag" || punct.as_char() != '=' {
                                        error!("tag error");
                                    }
                                }
                                _ => error!("attribute error"),
                            }

                            tag = if let Some(TokenTree::Literal(lit)) = stream.next() {
                                let str = lit.to_string();
                                <u8 as std::str::FromStr>::from_str(&str[1..str.len() - 1])?
                            } else {
                                error!("tag error");
                            } as i32;

                            tags.push(tag as u8);
                        }
                        _ => error!("wrong attribute"),
                    }
                }
                break;
            }
        }
    }

    let mut matches = vec![];
    let mut encodes = vec![];

    let tags_encoded_len: usize = tags.iter().map(|tag| if *tag < 0xF { 1 } else { 2 }).sum();

    for (i, tag) in tags.into_iter().enumerate() {
        let ident = &s.fields.iter().nth(i).unwrap().ident;

        let tag_to = quote!(#tag => );
        let read = quote!(::jce::types::JceType::read(
            buf,
            t,
            STRUCT_NAME,
            stringify!(#ident)
        )?);

        matches.push(quote!(#tag_to val.#ident = #read));
        encodes.push(quote!(::jce::types::JceType::write(&self.#ident, buf, #tag)));
    }

    Ok(quote! {
        impl #imp_generics ::jce::JceStruct for #name #ty_generics #where_clause {
            fn encode_raw<B: ::jce::bytes::BufMut>(&self, buf: &mut B) {
                #(#encodes);*;
            }

            fn encoded_len(&self) -> usize {
                #tags_encoded_len + #(#fields_encoded_len)+*
            }

            fn decode_raw<B: ::jce::bytes::Buf>(
                buf: &mut B,
                to_end: bool,
            ) -> ::jce::error::DecodeResult<Self> {
                const STRUCT_NAME: &str = stringify!(#name);

                let mut val = Self::default();

                let mut t = 0;
                while buf.remaining() > 0 {
                    let header = ::jce::de::read_header(buf)?;

                    t = header.value_type();
                    if !to_end && t == ::jce::types::STRUCT_END {
                        break;
                    }

                    match header.tag() {
                        #(#matches),*,
                        _ => ::jce::types::skip_field(buf, t)?,
                    }
                }

                Ok(val)
            }
        }

        impl #imp_generics ::core::default::Default for #name #ty_generics #where_clause {
            fn default() -> Self {
                Self {
                    #(#fields_default),*,
                }
            }
        }
    }
    .into())
}

fn try_jce_enum(input: TokenStream) -> Result<TokenStream, Box<dyn Error>> {
    let input: DeriveInput = syn::parse(input)?;

    let name = input.ident;
    let (imp_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let enum_data = match input.data {
        Data::Enum(e) => e,
        _ => error!("JceEnum can only derive for enums"),
    };

    // Generate Into<i32> implementation
    let mut into_match = vec![];
    let mut try_from_match = vec![];

    for (discriminant, variant) in enum_data.variants.iter().enumerate() {
        let ident = &variant.ident;
        let value = discriminant as i32;
        into_match.push(quote! {
            #name::#ident => #value,
        });
        try_from_match.push(quote! {
            #value => Ok(#name::#ident),
        });
    }

    // Handle explicit discriminants - if any variant has discriminant, use that instead of implicit
    let has_explicit = enum_data.variants.iter().any(|v| v.discriminant.is_some());
    if has_explicit {
        into_match.clear();
        try_from_match.clear();

        for variant in &enum_data.variants {
            let ident = &variant.ident;
            let (_, disc) = variant.discriminant.as_ref().unwrap();
            try_from_match.push(quote! {
                #disc => Ok(#name::#ident),
            });
            into_match.push(quote! {
                #name::#ident => #disc,
            });
        }
    }

    let first_variant = &enum_data.variants.first().unwrap().ident;
    Ok(quote! {
         impl #imp_generics ::jce::JceEnum for #name #ty_generics #where_clause {
         }

         impl #imp_generics From<#name #ty_generics> for i32 #where_clause {
             fn from(v: #name #ty_generics) -> Self {
                 match v {
                     #(#into_match)*
                 }
             }
         }

         impl #imp_generics TryFrom<i32> for #name #ty_generics #where_clause {
             type Error = i32;

             fn try_from(v: i32) -> Result<Self, Self::Error> {
                 match v {
                     #(#try_from_match)*
                     _ => Err(v),
                 }
             }
         }

         impl #imp_generics Default for #name #ty_generics #where_clause {
             fn default() -> Self {
                 #name::#first_variant
             }
         }

        impl #imp_generics ::jce::types::JceType for #name #ty_generics #where_clause {
            fn read<B: ::jce::bytes::Buf>(
                buf: &mut B,
                t: u8,
                struct_name: &'static str,
                field: &'static str,
            ) -> ::jce::error::DecodeResult<Self> {
                ::jce::types::jce_enum::read(buf, t, struct_name, field)
                    .map_err(|e| e.into())
            }

            fn write<B: ::jce::bytes::BufMut>(&self, buf: &mut B, tag: u8) {
                ::jce::types::jce_enum::write(self, buf, tag);
            }

            fn write_len(&self) -> usize {
                ::jce::types::jce_enum::write_len(self)
            }
        }
    }
    .into())
}
