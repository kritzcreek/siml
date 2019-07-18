use pretty::{BoxDoc, Doc};

pub fn parens_if(p: bool, s: String) -> String {
    if p {
        format!("({})", s)
    } else {
        s
    }
}

pub fn render_doc(doc: Doc<BoxDoc<()>>) -> String {
    render_doc_width(doc, 80)
}

pub fn render_doc_width(doc: Doc<BoxDoc<()>>, width: usize) -> String {
    let mut w = Vec::new();
    doc.render(width, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}
