//! Simple test to verify ARM64 module compilation

#[test]
fn test_arm64_module_exists() {
    // Just verify we can access ARM64 types
    use mmcc::arch::arm64::{X0, X1, PReg};
    
    let reg0 = X0;
    let reg1 = X1;
    
    assert_eq!(reg0.index(), 0);
    assert_eq!(reg1.index(), 1);
}