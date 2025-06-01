use crate::TinyString;


#[test]
fn simple() {
    let mut s = TinyString::<10>::new();

    for (i, c) in (b'0'..=b'9').enumerate() {
        s.push(c as char);
        assert_eq!(s.len(), i + 1);
    }

    s.push_str("hellooo");
}
