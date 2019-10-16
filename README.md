# Smart PathBuf

[![Build Status](https://travis-ci.com/DevinR528/smart-pathbuf.svg?branch=master)](https://travis-ci.com/DevinR528/smart-pathbuf)
[![Latest Version](https://img.shields.io/crates/v/smart-pathbuf.svg)](https://crates.io/crates/toml)

A wrapper around rust's `PathBuf` adding convenience methods for manipulating paths. `SmartPathBuf`
has all the same functionality as `PathBuf` and more, it is an extension and will always maintain feature
parity with `PathBuf`. `SmartPathBuf` will add some overhead as it needs to keep more information around,
I will work to keep it as low overhead as possible.

## Use
```toml
smart-pathbuf = "0.3"
```

## Examples
No more calling multiple `.pop()`.
```rust
use smart_path::SmartPathBuf;

let dir = std::env::current_dir().expect("failed");
let mut s_path = SmartPathBuf::from(&dir);
//or just s_path = SmartPathBuf::from(&dir);
// s_path.push(&dir);

s_path.push("to/file");
do_something(&s_path); // "current/dir/to/file"

// remove segments up to the initial path given
s_path.initial();
// or s_path.pop_last();
// "current/dir"
s_path.push("another/file");
do_more(&s_path);
```
`SmartPathBuf` can be manipulated with indexes and ranges.
```rust

```
