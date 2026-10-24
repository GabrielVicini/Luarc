fn main() {
    // Same arithmetic as the source program, including Luau's floor modulo
    // (`a - floor(a / b) * b`), so the comparison measures code generation rather
    // than a different remainder algorithm (Rust's `%` on f64 is `fmod`).
    let mut acc = 0.0f64;
    let mut i = 1.0f64;
    while i <= 30000000.0 {
        let a = acc + i * i;
        acc = a - (a / 1000003.0).floor() * 1000003.0;
        i += 1.0;
    }
    println!("{}", acc);
}
