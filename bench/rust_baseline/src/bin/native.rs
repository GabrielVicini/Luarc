fn main() {
    let mut acc = 0.0;
    for _ in 0..5_000_000 {
        acc = fixture::add(acc, 1.0);
    }
    let mut len = 0usize;
    for _ in 0..200_000 {
        len += fixture::greet("x").len();
    }
    let data: Vec<f64> = (1..=1000).map(|i| i as f64).collect();
    let mut best = 0.0;
    for _ in 0..2000 {
        best = fixture::largest(&data);
    }
    println!("{}\t{}\t{}", acc, len, best);
}
