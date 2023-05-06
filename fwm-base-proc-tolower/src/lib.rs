use proc_macro::{Literal, TokenStream, TokenTree};

/// Like stringify!() but also do lowercase.
///
/// # Example
/// ```
/// # use fwm_base_proc_tolower::lower;
/// assert_eq!(lower!(Foo), "foo");
/// ```
#[proc_macro]
pub fn lower(stream: TokenStream) -> TokenStream {
    let s = stream.to_string().to_lowercase();

    TokenTree::Literal(Literal::string(&s)).into()
}
