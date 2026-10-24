use std::collections::HashMap;

struct Point {
    x: f64,
    y: f64,
}

fn main() {
    let mut arr = Vec::new();
    for i in 1..=2_000_000u32 {
        arr.push(i as f64 * 0.5);
    }
    let sum: f64 = arr.iter().sum();
    let mut counts: HashMap<String, f64> = HashMap::new();
    for i in 1..=200_000u32 {
        *counts.entry(format!("k{}", i % 1000)).or_insert(0.0) += 1.0;
    }
    let mut points = Vec::new();
    for i in 1..=300_000u32 {
        points.push(Point { x: i as f64, y: i as f64 * 2.0 });
    }
    let total: f64 = points.iter().map(|p| p.x + p.y).sum();
    println!("{}\t{}\t{}", sum, counts["k7"], total);
}
