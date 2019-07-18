use pretty::{BoxDoc, Doc};

pub fn parens_if(p: bool, s: String) -> String {
    if p {
        format!("({})", s)
    } else {
        s
    }
}

pub fn render_doc(doc: Doc<BoxDoc<()>>) -> String {
    let mut w = Vec::new();
    doc.render(80, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

