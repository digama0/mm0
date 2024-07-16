#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate mmbp;

fuzz_target!(|data: &[u8]| {
    if let Ok(mmb) = mmbp::parser::MmbFile::parse(data) {
        for i in 0..data.len() {
            let term_id = mmbp::TermId(i as u32);
            let thm_id = mmbp::ThmId(i as u32);
            let _ = mmb.term(term_id);
            let _ = mmb.thm(thm_id);
        }
    }
});
