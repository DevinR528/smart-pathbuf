use criterion::{criterion_group, criterion_main, Criterion};
use smart_path::SmartPathBuf;

fn push_pop_bench(c: &mut Criterion) {
    let mut path = SmartPathBuf::from(std::env::current_dir().expect("no current dir"));
    c.bench_function("push pop smart path buffer", |b| {
        b.iter(|| {
            path.push("x/y/z");
            path.initial();
        })
    });
}

fn init_bench(c: &mut Criterion) {
    c.bench_function("initialize smart path buffer", |b| {
        b.iter(|| {
            let _path = SmartPathBuf::from(std::env::current_dir().expect("no current dir"));
        })
    });
}

criterion_group!(benches, push_pop_bench, init_bench);

criterion_main!(benches);
