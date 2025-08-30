
// Test add function with parameters
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    // Test 1: Simple add
    let result = add(10, 32);
    
    // Test 2: Access command line args
    let args: Vec<String> = std::env::args().collect();
    let argc = args.len();
    
    // Exit with result (should be 42)
    std::process::exit(result);
}
