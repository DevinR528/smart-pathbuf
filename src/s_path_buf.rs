use std::borrow::{Borrow, Cow};
use std::convert::Infallible;
use std::cmp::Ordering;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::iter::{Extend, FromIterator};
use std::ops::{Deref, Index, IndexMut, Range, RangeFrom, RangeFull, RangeTo};
use std::path::{Path, PathBuf};
use std::str::FromStr;

/// Allows `SmartPathBuf`s to be sliced using `Range` syntax.
///
/// # Example
/// ```
/// use std::path::PathBuf;
/// use smart_path::{SmartPathBuf, PathRange};
///
/// let mut path = SmartPathBuf::from("hello/world/bye");
/// let p = path.range(..path.len() - 1);
/// assert_eq!(p.as_path(), PathBuf::from("hello/world").as_path());
/// ```
pub trait PathRange<T: ?Sized> {
    fn range(&self, range: T) -> Self;
}

fn os_str_as_u8_slice(s: &OsStr) -> &[u8] {
    unsafe { &*(s as *const OsStr as *const [u8]) }
}

#[derive(Clone)]
pub struct SmartPathBuf {
    inner: PathBuf,
    len: usize,
    init: Option<usize>,
    segments: Vec<OsString>,
    indexes: Vec<usize>,
}

impl SmartPathBuf {
    /// Constructs a new `SmartPathBuf`.
    /// 
    /// # Examples
    /// ```
    /// use smart_path::SmartPathBuf;
    /// 
    /// let mut smart_path = SmartPathBuf::new();
    /// ```
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
    /// Returns a `Path` same as [`as_ref`] but more explicit.
    /// 
    /// [`as_ref`]: struct.SmartPathBuf.html#method.pop
    pub fn as_path(&self) -> &Path {
        self
    }
    /// `len` is the number of segments, on "*nix" systems
    /// if absolute this includes "/".
    pub fn len(&self) -> usize {
        self.len
    }
    /// If there are no segments in this path returns true.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// When pushing segments to a new `SmartPathBuf` first push sets the initial size,
    /// using one of the from methods also sets initial size.
    ///
    /// # Examples
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
        if self.init.is_some() {
            let seg = path
                .as_ref()
                .iter()
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
    /// 
    /// # Examples
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
    /// Resets `SmartPathBuf` to the initial path.
    /// 
    /// # Examples
    /// ```
    /// use std::path::PathBuf;
    /// use smart_path::SmartPathBuf;
    ///
    /// let mut path = SmartPathBuf::new();
    /// path.push("hello/world/bye");
    /// path.push("more/stuff");
    /// path.push("even/more");
    /// path.initial();
    /// assert_eq!(path.as_path(), PathBuf::from("hello/world/bye").as_path());
    /// ```
    pub fn initial(&mut self) {
        if let Some(init) = self.init {
            let start = self.len - init;
            for _ in 0..start {
                self.pop();
            }
        }
    }
    /// Updates `file_name` to the given file name.
    ///
    /// If `file_name` was `None`, this is equivalent to pushing
    /// another segment that is a file name.
    ///
    /// Otherwise it is equivalent to calling `pop` and then pushing
    /// a file name.
    ///
    /// # Examples
    ///
    /// ```
    /// use smart_path::SmartPathBuf;
    ///
    /// let mut buf = SmartPathBuf::from("/");
    /// assert!(buf.file_name() == None);
    /// buf.set_file_name("bar");
    /// assert!(buf == SmartPathBuf::from("/bar"));
    /// assert!(buf.file_name().is_some());
    /// buf.set_file_name("baz.txt");
    /// assert!(buf == SmartPathBuf::from("/baz.txt"));
    /// ```
    pub fn set_file_name<S: AsRef<OsStr>>(&mut self, file_name: S) {
        if self.inner.file_name().is_some() {
            self.pop();
        }
        self.push(file_name.as_ref());
    }
    /// Updates `extension` to the given extension.
    ///
    /// Returns `false` and does nothing if `file_name` is `None`,
    /// returns `true` and updates the extension otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::Path;
    /// use smart_path::SmartPathBuf;
    ///
    /// let mut p = SmartPathBuf::from("/feel/the");
    ///
    /// p.set_extension("force");
    /// assert_eq!(Path::new("/feel/the.force"), p.as_path());
    ///
    /// p.set_extension("dark_side");
    /// assert_eq!(Path::new("/feel/the.dark_side"), p.as_path());
    /// ```
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
    /// Boxes a `Path` up for you.
    pub fn into_boxed_path(self) -> Box<Path> {
        self.inner.into_boxed_path()
    }
    /// Returns a new `OsString`.
    pub fn into_os_string(self) -> OsString {
        self.inner.into_os_string()
    }

    #[cfg(feature = "unstable")]
    /// The amount the inner `Vec` is capable of holding.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    #[cfg(feature = "unstable")]
    /// Remove and reset everything.
    pub fn clear(&mut self) {
        self.inner.clear();
        self.segments.clear();
        self.indexes.clear();
        self.len = 0;
        self.init = None;
    }
    /// Reserve about `more` amount of capacity, the compiler may
    /// decide to reserve more than the suggested amount.
    #[cfg(feature = "unstable")]
    pub fn reserve(&mut self, more: usize) {
        self.inner.reserve(more);
        self.segments.reserve(more);
    }

    #[cfg(feature = "unstable")]
    /// Reserve exactly `more` amount of capacity.
    pub fn reserve_exact(&mut self, more: usize) {
        self.inner.reserve_exact(more);
        self.segments.reserve_exact(more);
    }

    #[cfg(feature = "unstable")]
    /// Shrink the inner `Vec` so there is no excess capacity. 
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
        self.segments.shrink_to_fit();
    }

    #[cfg(feature = "unstable")]
    /// Shrink the inner `Vec` to specified capacity.
    /// 
    /// # Safety
    /// this will panic if the given `min_cap` is larger than
    /// current capacity (you can not use this to grow the `Vec`). 
    pub fn shrink_to(&mut self, min_cap: usize) {
        self.inner.shrink_to(min_cap);
        self.segments.shrink_to(min_cap);
    }
}

impl<T> From<&T> for SmartPathBuf
where
    T: ?Sized + AsRef<OsStr>,
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

impl<P: AsRef<Path>> FromIterator<P> for SmartPathBuf {
    fn from_iter<I: IntoIterator<Item = P>>(iter: I) -> SmartPathBuf {
        let mut s_path = SmartPathBuf::new();
        s_path.extend(iter);
        s_path
    }
}

impl<P: AsRef<Path>> Extend<P> for SmartPathBuf {
    fn extend<I: IntoIterator<Item = P>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |p| self.push(p.as_ref()));
    }
}

impl<'a> IntoIterator for &'a SmartPathBuf {
    type Item = &'a OsStr;
    type IntoIter = std::path::Iter<'a>;
    fn into_iter(self) -> std::path::Iter<'a> { self.iter() }
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
    /// Constructs an empty `SmartPathBuf`.
    fn default() -> Self {
        SmartPathBuf::new()
    }
}

impl Hash for SmartPathBuf {
    /// Hashes the inner `Path` value not `SmartPathBuf`.
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.as_path().hash(h)
    }
}

impl PartialOrd for SmartPathBuf {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.components().partial_cmp(other.components())
    }
}

impl Ord for SmartPathBuf {
    fn cmp(&self, other: &Self) -> Ordering {
        self.components().cmp(other.components())
    }
}

impl Eq for SmartPathBuf {}

impl PartialEq for SmartPathBuf {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(other.as_path())
    }
}

macro_rules! impl_cmp {
    ($lhs:ty, $rhs: ty) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { <Path as PartialEq>::eq(self, other) }
        }

        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool { <Path as PartialEq>::eq(self, other) }
        }

        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                <Path as PartialOrd>::partial_cmp(self, other)
            }
        }

        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<Ordering> {
                <Path as PartialOrd>::partial_cmp(self, other)
            }
        }
    }
}

impl_cmp!(SmartPathBuf, PathBuf);
impl_cmp!(SmartPathBuf, Path);
impl_cmp!(SmartPathBuf, &'a Path);

macro_rules! impl_cmp_os_str {
    ($lhs:ty, $rhs: ty) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { <Path as PartialEq>::eq(self, other.as_ref()) }
        }

        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool { <Path as PartialEq>::eq(self.as_ref(), other) }
        }

        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                <Path as PartialOrd>::partial_cmp(self, other.as_ref())
            }
        }

        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<Ordering> {
                <Path as PartialOrd>::partial_cmp(self.as_ref(), other)
            }
        }
    }
}

impl_cmp_os_str!(SmartPathBuf, OsStr);
impl_cmp_os_str!(SmartPathBuf, &'a OsStr);
impl_cmp_os_str!(SmartPathBuf, Cow<'a, OsStr>);
impl_cmp_os_str!(SmartPathBuf, OsString);

macro_rules! index_impl {
    ($typ:ty, $out:ty) => {
        impl Index<$typ> for SmartPathBuf {
            type Output = $out;
            /// On unix the `/` is always the first element in a Path
            #[inline]
            fn index(&self, rng: $typ) -> &Self::Output {
                &self.segments[rng]
            }
        }
    };
}

macro_rules! index_mut_impl {
    ($typ:ty, $out:ty) => {
        impl IndexMut<$typ> for SmartPathBuf {
            /// On unix the `/` is always the first element in a Path
            #[inline]
            fn index_mut(&mut self, rng: $typ) -> &mut Self::Output {
                &mut self.segments[rng]
            }
        }
    };
}

impl Index<usize> for SmartPathBuf {
    type Output = OsString;
    #[inline]
    fn index(&self, idx: usize) -> &Self::Output {
        &self.segments[idx]
    }
}
index_impl!(Range<usize>, [OsString]);
index_impl!(RangeFull, [OsString]);
index_impl!(RangeFrom<usize>, [OsString]);
index_impl!(RangeTo<usize>, [OsString]);

impl IndexMut<usize> for SmartPathBuf {
    #[inline]
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        &mut self.segments[idx]
    }
}
index_mut_impl!(Range<usize>, [OsString]);
index_mut_impl!(RangeFull, [OsString]);
index_mut_impl!(RangeFrom<usize>, [OsString]);
index_mut_impl!(RangeTo<usize>, [OsString]);

macro_rules! index_mut_smartpath_impl {
    ($typ:ty, #[$meta:meta]) => {
        impl PathRange<$typ> for SmartPathBuf {
            #[$meta]
            fn range(&self, range: $typ) -> Self {
                let sep = if std::path::is_separator('/') {
                    "/"
                } else {
                    "\\"
                };
                let is_root = self.segments.first() == Some(&OsString::from(sep));
                let p = self.segments[range]
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        let seg = p.to_str().unwrap();
                        if i == 1 && is_root || i == 0 {
                            seg.to_string()
                        } else {
                            format!("{}{}", sep, seg)
                        }
                    })
                    .collect::<String>();
                // unwrap should be ok we had a valid path before
                SmartPathBuf::from_str(&p).unwrap_or_default()
            }
        }
    };
}

index_mut_smartpath_impl!(
    RangeFull,
    #[doc="Returns a new `SmartPath` from the range provided"]
);

index_mut_smartpath_impl!(
    RangeTo<usize>,
    #[doc="Returns a new `SmartPath` from the range provided"]
);

impl PathRange<RangeFrom<usize>> for SmartPathBuf {
    /// Returns a new `SmartPath` from the range provided
    fn range(&self, range: RangeFrom<usize>) -> Self {
        let sep = if std::path::is_separator('/') {
            "/"
        } else {
            "\\"
        };
        let is_root = self.segments.get(range.start) == Some(&OsString::from(sep));
        let p = self.segments[range]
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let seg = p.to_str().unwrap();
                if i == 1 && is_root || i == 0 {
                    seg.to_string()
                } else {
                    format!("{}{}", sep, seg)
                }
            })
            .collect::<String>();
        // unwrap should be ok we had a valid path before
        SmartPathBuf::from_str(&p).unwrap_or_default()
    }
}
impl PathRange<Range<usize>> for SmartPathBuf {
    /// Returns a new `SmartPath` from the range provided
    fn range(&self, range: Range<usize>) -> Self {
        let sep = if std::path::is_separator('/') {
            "/"
        } else {
            "\\"
        };
        let is_root = self.segments.get(range.start) == Some(&OsString::from(sep));
        let p = self.segments[range]
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let seg = p.to_str().unwrap();
                if i == 1 && is_root || i == 0 {
                    seg.to_string()
                } else {
                    format!("{}{}", sep, seg)
                }
            })
            .collect::<String>();
        // unwrap should be ok we had a valid path before
        SmartPathBuf::from_str(&p).unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
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
                $init_len, s_path.len,
                "initial smart path len {} init {}",
                s_path.len, $init_len
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
            let seg_path = PathBuf::from_str(s_path.range(..).as_os_str().to_str().unwrap());
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

    #[test]
    fn test_eq_ord() {
        let s = SmartPathBuf::from_str("folder/file").unwrap();

        assert!(s == Path::new("folder/file"));
        assert!(s == PathBuf::from("folder/file"));
        assert!(s == OsStr::new("folder/file"));
        assert!(s == OsString::from("folder/file"));
        assert!(s == *OsStr::new("folder/file"));

        assert!(s > Path::new("a"));
        assert!(s > PathBuf::from("a"));
        assert!(s > OsStr::new("a"));
        assert!(s > OsString::from("a"));
        assert!(s > *OsStr::new("a"));
    }

    #[test]
    fn test_range() {
        let s = SmartPathBuf::from_str("/home/hello/../knuth").unwrap();

        assert_eq!(Path::new("/home/hello/../knuth"), s.range(..).as_path());
        assert_eq!(Path::new("home/hello/../knuth"), s.range(1..).as_path());
        assert_eq!(Path::new("hello/../knuth"), s.range(2..).as_path());
        assert_eq!(Path::new("/home/hello/"), s.range(..3).as_path());
        assert_eq!(Path::new("home"), s.range(1..2).as_path());
        assert_eq!(
            Path::new("/home/hello/../knuth"),
            s.range(0..s.len()).as_path()
        );
    }

    #[test]
    fn seg_join() {
        let s = SmartPathBuf::from_str("/home/hello/../knuth").unwrap();
        let seg_path = s.range(..);
        assert_eq!(s, seg_path, "segments collected");
    }

    #[test]
    #[cfg(not(windows))]
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
            init_len: 2,
            push: ["windows", "hello", "bye"],
            push_len: 5,
            pop_count: 2,
            pop_len: 3,
            cmp: "c:\\windows",
            sep_char: "",
        );
    }

    #[test]
    fn test_froms() {
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
        assert_eq!(
            path.segments,
            [
                OsString::from("hello"),
                OsString::from("world"),
                OsString::from("bye")
            ]
        );

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
    fn test_pop_last() {
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
