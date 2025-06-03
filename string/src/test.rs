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

#[test]
fn drain_test() {
    let mut s = TinyString::<10>::from("abcdefghijk");

    let mut drain = s.drain(2..=4);
    assert_eq!(drain.next(), Some('c'));
    assert_eq!(drain.next_back(), Some('e'));
    assert_eq!(drain.next(), Some('d'));
    drop(drain);

    assert_eq!(s.as_str(), "abfghijk");
}

#[test]
fn drain_keep_rest() {
    let mut s = TinyString::<10>::from("abcdefghijk");

    let mut drain = s.drain(2..=5);
    assert_eq!(drain.next(), Some('c'));
    assert_eq!(drain.next_back(), Some('f'));
    assert_eq!(drain.next(), Some('d'));
    drain.keep_rest();

    assert_eq!(s.as_str(), "abeghijk");
}
