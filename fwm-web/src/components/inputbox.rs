use dioxus::prelude::*;

#[derive(Props)]
pub struct InputboxProps<'a> {
    default_text: &'a str,
    lang: &'a str,
    on_change: EventHandler<'a, String>,
}

pub fn Inputbox<'a>(cx: Scope<'a, InputboxProps<'a>>) -> Element<'a> {
    cx.render(rsx! {
        div {
            class: "codeblock",
            div {
                class: "prelude",
                "{cx.props.lang}"
            },
            textarea {
                spellcheck: "false",
                onchange: |e| cx.props.on_change.call(e.value.clone()),
                "{cx.props.default_text}"
            }
        }
    })
}
