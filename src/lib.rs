//! Wrapper around PathBuf to provide extra features for popping,
//! pushing, indexing and generally manipulating Paths. All the same
//! conversions and method signatures are possible, making `SmartPathBuf`
//!  isomorphic to `PathBuf`. 
//! 
//! ## Examples where useful
//! ```
//! use smart_path::SmartPathBuf;
//! 
//! let dir = std::env::current_dir().expect("failed");
//! let mut s_path = SmartPathBuf::from(&dir);
//! s_path.push("to/file");
//! // do_something(&s_path); // "current/dir/to/file"
//! s_path.initial();
//! // "current/dir"
//! s_path.push("another/file");
//! // do_more(&s_path);
//! ```
//! 

mod s_path_buf;
pub use s_path_buf::SmartPathBuf;

