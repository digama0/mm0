#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate mmbp;

fuzz_target!(|data: &[u8]| {
    if let Ok(mmb) = mmbp::parser::MmbFile::parse(data) {
        for declar in mmb.proof() {
            match declar {
                Ok((_, proof)) => {
                    for elem in proof {
                        match elem {
                            Ok(..) => continue,
                            Err(_) => break
                        }
                    }
                },
                _ => break
            }
        }
    }
});