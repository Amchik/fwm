use dioxus::prelude::*;

#[derive(Props)]
pub struct CodeboxProps<'a> {
    lang: &'a str,
    children: Element<'a>,
}

pub fn Codebox<'a>(cx: Scope<'a, CodeboxProps<'a>>) -> Element<'a> {
    cx.render(rsx! {
        div {
            class: "codeblock",
            div {
                class: "prelude",
                "{cx.props.lang}"
            },
            pre {
                spellcheck: "false",
                &cx.props.children
            }
        }
    })
}
