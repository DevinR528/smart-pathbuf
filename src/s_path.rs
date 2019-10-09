use std::path::{Path};

pub struct SmartPath {
    inner: Box<Path>,
    init: usize,
    indexes: Vec<usize>,
}
