use std::borrow::Borrow;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Debug};
use std::str::FromStr;
use std::path::{Path, PathBuf};
use std::ops::Deref;

pub struct SmartPathBuf {
    inner: PathBuf,
    len: usize,
    init: Option<usize>,
    segments: Vec<
    indexes: Vec<usize>,
}

impl SmartPathBuf {
    pub fn new() -> SmartPathBuf {
        Self {
            inner: PathBuf::new(),
            len: 0,
            init: None,
            indexes: Vec::new(),
        }
    }
    fn with_inner(inner: PathBuf, init: Option<usize>, len: usize) -> Self {
        SmartPathBuf {
            inner,
            len,
            init,
            indexes: Vec::new(),
        }
    }
    #[cfg(feature = "unstable")]
    pub fn with_capacity(cap: usize) -> SmartPathBuf {
        Self {
            inner: PathBuf::with_capacity(cap),
            len: 0,
            init: None,
            indexes: Vec::new(),
        }
    }
    pub fn as_path(&self) -> &Path {
        self
    }
    /// When pushing segments to a new `SmartPathBuf` first push sets the initial size,
    /// using one of the from methods also sets initial size.
    /// 
    /// # Example
    /// ```
    /// use std::path::PathBuf;
    /// use smart_path::SmartPathBuf;
    /// 
    /// let mut path = SmartPathBuf::new();
    /// path.push("hello/world/bye");
    /// path.push("more/stuff");
    /// path.initial();
    /// assert_eq!(path.as_path(), PathBuf::from("hello/world/bye").as_path());
    /// ```
    pub fn push<P: AsRef<Path>>(&mut self, path: P) {
        if let Some(_) = self.init {
            let seg = path.as_ref().iter().map(|os| os.to_os_string()).collect::<Vec<_>>();
            let len = seg.len();
            self.len += len;
            self.indexes.push(len);           
            self.inner.push(path);
        } else {
            let seg = path.as_ref().iter().count();
            self.len += seg;
            self.init = Some(seg);
            self.inner.push(path);
        }
    }
    // TODO make more efficient ??
    pub fn pop(&mut self) -> bool {
        if let Some(last_idx) = self.indexes.last_mut() {
            if *last_idx == 1 {
                self.indexes.pop();
            } else {
                *last_idx -= 1;
            }
        }
        self.len -= 1;
        self.inner.pop()
    }
    pub fn pop_last(&mut self) {
        if let Some(last) = self.indexes.pop() {
            for _ in 0..last {
                self.pop();
            }
        }
    }
    pub fn initial(&mut self) {
        if let Some(init) = self.init {
            let start = self.len - init;
            for _ in 0..start {
                self.pop();
            }
        }
    }
    pub fn set_file_name<S: AsRef<OsStr>>(&mut self, f: S) {

    }
}

impl<T> From<&T> for SmartPathBuf 
where
    T: ?Sized + AsRef<OsStr>
{
    fn from(s: &T) -> SmartPathBuf {
        SmartPathBuf::from(s.as_ref().to_os_string())
    }
}

impl From<OsString> for SmartPathBuf {
    fn from(s: OsString) -> SmartPathBuf {
        let inner = PathBuf::from(s);
        let len = inner.iter().count();
        let init = Some(len);
        SmartPathBuf::with_inner(inner, init, len)
    }
}

impl From<PathBuf> for SmartPathBuf {
    fn from(s: PathBuf) -> SmartPathBuf {
        let len = s.iter().count();
        let init = Some(len);
        SmartPathBuf::with_inner(s, init, len)
    }
}

impl FromStr for SmartPathBuf {
    type Err = core::convert::Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(SmartPathBuf::from(s))
    }
}

impl Borrow<Path> for SmartPathBuf {
    fn borrow(&self) -> &Path {
        self.deref()
    }
}

impl Debug for SmartPathBuf {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, formatter)
    }
}

impl Deref for SmartPathBuf {
    type Target = Path;
    fn deref(&self) -> &Path {
        Path::new(&self.inner)
    }
}

impl Default for SmartPathBuf {
    fn default() -> Self {
        SmartPathBuf::new()
    }
}

impl std::ops::Index

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_froms() {
        let dir = std::env::current_dir().expect("");
        let spd = SmartPathBuf::from(dir);

        let pb = PathBuf::from_str("hello/bye").expect("pathbuf failed");
        let os = OsString::from("hello/bye");

        let spb = SmartPathBuf::from(&pb);
        let sos = SmartPathBuf::from(&os);

        let spb_ref: &OsStr = spb.as_ref();
        let os_ref: &OsStr = os.as_ref();
        assert_eq!(spb_ref, os_ref);

        let sos_ref: &Path = sos.as_ref();
        let p_ref: &Path = pb.as_ref();
        assert_eq!(sos_ref, p_ref);
    }

    #[test]
    fn test_push() {
        let mut path = SmartPathBuf::new();
        assert!(path.init.is_none());
        path.push("hello/world/bye");
        assert_eq!(path.init, Some(3));
        assert!(path.indexes.is_empty());
        
        let p: &Path = path.as_ref();
        assert_eq!(p, Path::new("hello/world/bye"));
    }

    #[test]
    fn test_pop() {
        let mut tp = SmartPathBuf::from("");
        tp.push("some");
        tp.pop();

        let mut path = SmartPathBuf::from("from/you");
        assert_eq!(path.len, 2);
        path.push("hello");
        path.push("hello/bye");
        assert_eq!(path.len, 5);
        path.push("hello");
        // path.push("hello/world/bye");
        path.pop();
        assert_eq!(path.init, Some(2));
        assert_eq!(path.indexes, vec![1, 2]);
        let p: &Path = path.as_ref();
        assert_eq!(p, Path::new("from/you/hello/hello/bye"));
    }

    #[test]
    fn test_initial() {
        let mut path = SmartPathBuf::from("from/you");
        assert_eq!(path.len, 2);
        path.push("hello");
        path.push("hello/bye");
        assert_eq!(path.len, 5);
        path.push("hello");

        path.initial();
        assert!(path.indexes.is_empty());
        let s: &OsStr = path.as_ref();
        let s = s.to_str().expect("");
        assert_eq!(s, "from/you")
    }

    #[test]
    fn test_pop_last()  {
        let mut path = SmartPathBuf::from("from/you");
        assert_eq!(path.len, 2);
        path.push("hello");
        path.push("hello/bye");
        assert_eq!(path.init, Some(2));
        assert_eq!(path.len, 5);
        path.pop_last();
        assert_eq!(path.len, 3);
        let p: &Path = path.as_ref();
        assert_eq!(p, Path::new("from/you/hello"));
    }

}
