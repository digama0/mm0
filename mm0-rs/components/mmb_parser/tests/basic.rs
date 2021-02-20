use mmb_parser::parser::MmbFile;
use std::fs::OpenOptions;
use std::io::Read;
use std::path::PathBuf;

#[test]
fn peano0() {
    let mut mmb_bytes = Vec::new();
    let mut mmb_file = OpenOptions::new()
        .read(true)
        .truncate(false)
        .open(&PathBuf::from("./test_resources/peano.mmb"))
        .unwrap();
    mmb_file.read_to_end(&mut mmb_bytes).unwrap();
    assert!(!mmb_bytes.is_empty());
    assert!(MmbFile::parse(mmb_bytes.as_slice()).is_ok());
}
