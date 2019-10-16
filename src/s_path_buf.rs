use std::borrow::Borrow;
use std::convert::Infallible;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Debug};
use std::ops::{Bound, Deref, Range, RangeBounds, RangeFrom, RangeTo, RangeFull, Index, IndexMut};
use std::path::{Path, PathBuf};
use std::str::FromStr;

#[derive(Clone)]
pub struct SmartPathBuf {
    inner: PathBuf,
    len: usize,
    init: Option<usize>,
    segments: Vec<OsString>,
    indexes: Vec<usize>,
}

impl SmartPathBuf {
    pub fn new() -> SmartPathBuf {
        Self {
            inner: PathBuf::new(),
            len: 0,
            init: None,
            segments: Vec::new(),
            indexes: Vec::new(),
        }
    }
    fn with_inner(inner: PathBuf, init: Option<usize>, len: usize) -> Self {
        let segments = inner.iter().map(|s| s.to_os_string()).collect();
        SmartPathBuf {
            inner,
            len,
            init,
            segments,
            indexes: Vec::new(),
        }
    }

    /// ¯\\_(ツ)_/¯
    fn collect(&self, from: usize, to: usize) -> SmartPathBuf {
        let sep = if std::path::is_separator('/') { "/" } else { "\\" };
        let is_root = self.is_absolute();

        let p = self.segments[from..to]
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let seg = p.to_str().unwrap();
                if (i == 0 || i == 1) && is_root {
                    format!("{}", seg)
                } else {
                    format!("{}{}", sep, seg)
                }
            })
            .collect::<String>();
        // unwrap should be ok we had a valid path before
        SmartPathBuf::from_str(&p).unwrap_or_default()
    }

    #[cfg(feature = "unstable")]
    pub fn with_capacity(cap: usize) -> SmartPathBuf {
        Self {
            inner: PathBuf::with_capacity(cap),
            len: 0,
            init: None,
            segments: Vec::new(),
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
    /// // or
    /// let mut path = SmartPathBuf::from("hello/world/bye");
    /// 
    /// path.push("more/stuff");
    /// path.initial();
    /// assert_eq!(path.as_path(), PathBuf::from("hello/world/bye").as_path());
    /// ```
    pub fn push<P: AsRef<Path>>(&mut self, path: P) {
        if let Some(_) = self.init {
            let seg = path.as_ref().iter()
                .map(|os| os.to_os_string())
                .collect::<Vec<_>>();
            
            self.len += seg.len();
            self.indexes.push(seg.len());           
            self.segments.extend(seg);

            self.inner.push(path);
        } else {
            let seg = path.as_ref().iter();
            self.segments = seg.map(|s| s.to_os_string()).collect();
            self.len += self.segments.len();
            self.init = Some(self.len);

            self.inner.push(path);
        }
    }
    // TODO make more efficient ??
    /// Remove segment from end of path.
    pub fn pop(&mut self) -> bool {
        if let Some(last_idx) = self.indexes.last_mut() {
            if *last_idx == 1 {
                self.indexes.pop();
            } else {
                *last_idx -= 1;
            }
        }
        self.len -= 1;
        self.segments.pop();
        self.inner.pop()
    }
    /// Remove the last added segment(s) from end of path.
    /// # Example
    /// ```
    /// use std::path::PathBuf;
    /// use smart_path::SmartPathBuf;
    /// 
    /// let mut path = SmartPathBuf::new();
    /// path.push("hello/world/bye");
    /// path.push("more/stuff");
    /// path.pop_last();
    /// assert_eq!(path.as_path(), PathBuf::from("hello/world/bye").as_path());
    /// ```
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
    pub fn set_file_name<S: AsRef<OsStr>>(&mut self, file_name: S) {
        if self.inner.file_name().is_some() {
            self.pop();
        }
        self.push(file_name.as_ref());
    }
    pub fn set_extension<S: AsRef<OsStr>>(&mut self, extension: S) -> bool {
        if self.inner.file_name().is_none() {
            return false;
        }
        let mut stem = match self.file_stem() {
            Some(stem) => stem.to_os_string(),
            None => OsString::new(),
        };

        if !os_str_as_u8_slice(extension.as_ref()).is_empty() {
            stem.push(".");
            stem.push(extension);
        }
        // add to segments and inner
        self.set_file_name(&stem);
        true
    }
    pub fn into_boxed_path(self) -> Box<Path> {
        self.inner.into_boxed_path()
    }
    pub fn into_os_string(self) -> OsString {
        self.inner.into_os_string()
    }

    #[cfg(feature = "unstable")]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    #[cfg(feature = "unstable")]
    pub fn clear(&mut self) {
        self.inner.clear();
        self.segments.clear();
        self.indexes.clear();
        self.len = 0;
        self.init = None;
    }

    #[cfg(feature = "unstable")]
    pub fn reserve(&mut self, more: usize) {
        self.inner.reserve(more)
    }

     #[cfg(feature = "unstable")]
    pub fn reserve_exact(&mut self, more: usize) {
        self.inner.reserve_exact(more)
    }

     #[cfg(feature = "unstable")]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

     #[cfg(feature = "unstable")]
    pub fn shrink_to(&mut self, min_cap: usize) {
        self.inner.shrink_to(min_cap)
    }
}

fn os_str_as_u8_slice(s: &OsStr) -> &[u8] {
    unsafe { &*(s as *const OsStr as *const [u8]) }
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

impl From<String> for SmartPathBuf {
    fn from(s: String) -> SmartPathBuf {
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
    type Err = Infallible;

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

impl PartialEq for SmartPathBuf {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(other.as_path())
    }
}

trait Lazy<P: AsRef<OsStr>> {
    fn join(&self) -> P;
}

impl Lazy<OsString> for &[OsString] {
    fn join(&self) -> OsString {
        self.iter().fold(OsString::new(), |mut os, seg| {
            os.push(seg);
            os
        })
    }
}

pub struct LazyPath<'a>(&'a [OsString]);
// pub struct LazyPath<P: AsRef<OsStr>>(P);

impl<P: AsRef<OsStr>> Lazy<&OsStr> for LazyPath<P> {
    fn join(&self) -> &OsStr {
        &self.join()
    }
}

impl<P: AsRef<OsStr>> Deref for LazyPath<P> {
    type Target = Path;
    fn deref(&self) -> &Self::Target {
        Path::new(&self.join())
    }
}

impl<P: AsRef<OsStr>> AsRef<OsStr> for LazyPath<P> {
    fn as_ref(&self) -> &OsStr {
        self.join()
    }
}

impl Index<RangeFull> for SmartPathBuf {
    type Output = LazyPath<OsString>;
    /// On unix the `/` is always the first element in a Path
    fn index(&self, index: RangeFull) -> &Self::Output {
        LazyPath(&self.segments[index])
    }
}

macro_rules! index_impl {
    ($typ:ty, $out:ty) => {
        impl Index<$typ> for SmartPathBuf {
            type Output = $out;
            /// On unix the `/` is always the first element in a Path
            fn index(&self, index: $typ) -> &Self::Output {
                &self.segments[index]
            }
        }
    };
}

macro_rules! index_mut_impl {
    ($typ:ty, $out:ty) => {
        impl IndexMut<$typ> for SmartPathBuf {
            fn index_mut(&mut self, index: $typ) -> &mut Self::Output {
                &mut self.segments[index]
            }
        }
    };
}

// index_impl!(usize, OsString);
// index_impl!(Range<usize>, [OsString]);
// index_impl!(RangeFull, [OsString]);
// index_impl!(RangeFrom<usize>, [OsString]);
// index_impl!(RangeTo<usize>, [OsString]);

index_mut_impl!(usize, OsString);
index_mut_impl!(Range<usize>, [OsString]);
index_mut_impl!(RangeFull, [OsString]);
index_mut_impl!(RangeFrom<usize>, [OsString]);
index_mut_impl!(RangeTo<usize>, [OsString]);

#[cfg(test)]
mod tests {

    macro_rules! testy {
        // tests push and pop counts for segments, initial and len
        (
            start: $start:expr,
            init_len: $init_len:expr,
            push: $push:expr,
            push_len: $push_len:expr,
            pop_count: $pop_count:expr,
            pop_len: $pop_len:expr,
            cmp: $cmp:expr,
            sep_char: $sep_char:expr,
        ) => {
            let mut s_path = SmartPathBuf::from($start);
            assert_eq!(
                $init_len,
                s_path.len,
                "initial smart path len {} init {}",
                s_path.len,
                $init_len
            );
            assert_eq!(
                $init_len,
                s_path.segments.len(),
                "segments init len {} {}",
                s_path.segments.len(),
                $init_len,
            );

            for p in $push.iter() {
                s_path.push(p)
            }
            assert_eq!($push_len, s_path.len);
            assert_eq!($push_len, s_path.segments.len());

            for _ in 0..$pop_count {
                s_path.pop();
            }
            assert_eq!($pop_len, s_path.len);
            assert_eq!($pop_len, s_path.segments.len());

            let expected = PathBuf::from(&$cmp);
            assert_eq!(&expected, s_path.as_path());
            let seg_path = PathBuf::from_str(s_path.collect(0, s_path.len).as_os_str().to_str().unwrap());
            assert_eq!(expected, seg_path.unwrap(), "segments collected");
        };
        // tests initial
        (
            start: $start:expr,
            init_len: $init_len:expr,
            push: $push:expr,
            push_len: $push_len:expr,
            cmp: $cmp:expr,
        ) => {
            let mut s_path = SmartPathBuf::from($start);
            assert_eq!($init_len, s_path.len);
            assert_eq!(Some($init_len), s_path.init);
            assert_eq!($init_len, s_path.segments.len());

            for p in $push.iter() {
                s_path.push(p)
            }

            assert_eq!($push_len, s_path.len);
            assert_eq!($push_len, s_path.segments.len());

            s_path.initial();

            assert_eq!($init_len, s_path.len, "Initial len");
            assert_eq!(Some($init_len), s_path.init);
            assert_eq!($init_len, s_path.segments.len());

            assert_eq!(&PathBuf::from(&$cmp), s_path.as_path());
        };
        // tests pop_* methods
        (
            start: $start:expr,
            init_len: $init_len:expr,
            push: $push:expr,
            push_len: $push_len:expr,
            call: $call:ident,
            pop_len: $pop_len:expr,
            cmp: $cmp:expr,
        ) => {
            let mut s_path = SmartPathBuf::from($start);
            assert_eq!($init_len, s_path.len);
            assert_eq!(Some($init_len), s_path.init);
            assert_eq!($init_len, s_path.segments.len());

            for p in $push.iter() {
                s_path.push(p)
            }

            assert_eq!($push_len, s_path.len);
            assert_eq!($push_len, s_path.segments.len());

            s_path.$call();

            assert_eq!($pop_len, s_path.len);
            assert_eq!($pop_len, s_path.segments.len());

            assert_eq!(&PathBuf::from(&$cmp), s_path.as_path());
        };
        // tests file name and extension methods
        (
            start: $start:expr,
            cmp: $cmp:expr,
            file_name: $file_name:expr,
            extension: $extension:expr,
        ) => {
            let mut s_path = SmartPathBuf::from($start);

            s_path.set_file_name(&$file_name);
            let stem = s_path.file_stem().map(|p| p.to_str().unwrap()).unwrap();
            let expected_stem: &str = $file_name;
            assert_eq!(expected_stem, stem);

            s_path.set_extension(&$extension);
            let ext = s_path.extension().map(|p| p.to_str().unwrap()).unwrap();
            let expected_ext: &str = $extension;
            assert_eq!(expected_ext, ext);

            assert_eq!(&PathBuf::from(&$cmp), s_path.as_path());
        };
    }

    use super::*;

    #[test]
    fn seg_join() {
        let s = SmartPathBuf::from_str("/home/hello/../knuth").unwrap();

        let seg_path = s.collect(0, s.len);

        assert_eq!(s, seg_path, "segments collected");
    }

    #[test]
    fn test_unix() {
        testy!(
            start: "/home/file.txt",
            cmp: "/home/file.txt",
            file_name: "file",
            extension: "txt",
        );

        testy!(
            start: "/home",
            init_len: 2,
            push: ["linux", "hello", "bye"],
            push_len: 5,
            cmp: "/home",
        );

        testy!(
            start: "/home",
            init_len: 2,
            push: ["linux", "hello/bye"],
            push_len: 5,
            call: pop_last,
            pop_len: 3,
            cmp: "/home/linux",
        );

        testy!(
            start: "/home",
            init_len: 2,
            push: ["linux", "hello", "bye"],
            push_len: 5,
            pop_count: 2,
            pop_len: 3,
            cmp: "/home/linux",
            sep_char: "/",
        );
    }

    #[test]
    #[cfg(windows)]
    fn test_windows() {
        testy!(
            start: "c:\\",
            init_len: 1,
            push: ["windows", "hello", "bye"],
            push_len: 4,
            pop_count: 2,
            pop_len: 2,
            cmp: "c:\\windows",
            sep_char: "",
        );
    }

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
        assert_eq!(path.segments, [OsString::from("hello"), OsString::from("world"), OsString::from("bye")]);
        
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
        assert_eq!(path.segments.len(), 2);
        path.push("hello");
        path.push("hello/bye");
        assert_eq!(path.segments.len(), 5);
        assert_eq!(path.len, 5);
        path.push("hello");
        // path.push("hello/world/bye");
        path.pop();
        assert_eq!(path.segments.len(), 5);
        assert_eq!(path.len, 5);
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
