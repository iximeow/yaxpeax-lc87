use yaxpeax_arch::Decoder;

fn test_display(data: &[u8], expected: &'static str) {
    let mut reader = yaxpeax_arch::U8Reader::new(data);
    match yaxpeax_lc87::InstDecoder::default().decode(&mut reader) {
        Ok(instr) => {
            let displayed = instr.to_string();
            assert_eq!(&displayed, expected);
            assert_eq!(data.len() as u8, instr.len());
        }
        Err(e) => {
            panic!("failed to decode {:02x?}: {}", data, e);
        }
    }
}

#[test]
fn test_disassembly() {
//    test_display(&[0x43, 0x0a, 0x1f], "mov #13h, spl");
    test_display(&[0x43, 0x0a, 0x1f], "mov #1fh, fe0ah");
//    test_display(&[0x43, 0x0b, 0x00], "mov #00h, sph");
    test_display(&[0x43, 0x0b, 0x00], "mov #00h, fe0bh");
    test_display(&[0x47, 0x34, 0x12], "ldw #1234h");
    test_display(&[0x47, 0x78, 0x56], "ldw #5678h");
    test_display(&[0x97, 0x12, 0xfe], "stw fe12h");
    test_display(&[0x97, 0xc0, 0x00], "stw 00c0h");
    test_display(&[0x49, 0x00], "rcall $+0x100");
    test_display(&[0x59, 0x00], "rcall $+0x900");
    test_display(&[0x08, 0x10, 0x3f], "bp 0010h, 0, $+0x3f");
    test_display(&[0x0a, 0x10, 0x3f], "bp 0010h, 2, $+0x3f");
}
