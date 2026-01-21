use std::{fmt::Debug, ops::Range};

use crate::IntervalTree;

/// A view into a single entry in an [`IntervalTree`], which may either be
/// vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`IntervalTree`].
///
/// [`entry`]: IntervalTree::entry
#[derive(Debug)]
pub enum Entry<'a, R, V>
where
    R: Ord + Clone + Debug,
{
    /// A vacant entry.
    Vacant(VacantEntry<'a, R, V>),
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, R, V>),
}

/// A view into a vacant entry in an [`IntervalTree`].
/// It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct VacantEntry<'a, R, V>
where
    R: Ord + Clone + Debug,
{
    key: Range<R>,
    tree: &'a mut IntervalTree<R, V>,
}

/// A view into an occupied entry in an [`IntervalTree`].
/// It is part of the [`Entry`] enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, R, V>
where
    R: Ord + Clone + Debug,
{
    key: Range<R>,
    tree: &'a mut IntervalTree<R, V>,
}

impl<'a, R, V> VacantEntry<'a, R, V>
where
    R: Ord + Clone + Debug,
{
    /// Gets a reference to the key that would be used when inserting a value
    /// through the VacantEntry.
    #[inline]
    pub fn key(&self) -> &Range<R> {
        &self.key
    }

    /// Take ownership of the key.
    #[inline]
    pub fn into_key(self) -> Range<R> {
        self.key
    }

    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it.
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        self.tree.insert(self.key.clone(), value);
        self.tree.get_mut(&self.key).unwrap()
    }
}

impl<'a, R, V> OccupiedEntry<'a, R, V>
where
    R: Ord + Clone + Debug,
{
    /// Gets a reference to the key in the entry.
    #[inline]
    pub fn key(&self) -> &Range<R> {
        &self.key
    }

    /// Gets a reference to the value in the entry.
    #[inline]
    pub fn get(&self) -> &V {
        self.tree.get(&self.key).unwrap()
    }

    /// Gets a mutable reference to the value in the entry.
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        self.tree.get_mut(&self.key).unwrap()
    }

    /// Converts the entry into a mutable reference to its value.
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        self.tree.get_mut(&self.key).unwrap()
    }

    /// Sets the value of the entry with the OccupiedEntry's key,
    /// and returns the entry's old value.
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        self.tree.insert(self.key.clone(), value).unwrap()
    }

    /// Takes the value of the entry out of the tree, and returns it.
    #[inline]
    pub fn remove(self) -> V {
        self.tree.remove(&self.key).unwrap()
    }
}

impl<'a, R, V> Entry<'a, R, V>
where
    R: Ord + Clone + Debug,
{
    /// Create a new Entry for the given key and tree.
    pub(crate) fn new(key: Range<R>, tree: &'a mut IntervalTree<R, V>) -> Self {
        if tree.contains_key(&key) {
            Entry::Occupied(OccupiedEntry { key, tree })
        } else {
            Entry::Vacant(VacantEntry { key, tree })
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use interavl::IntervalTree;
    ///
    /// let mut tree: IntervalTree<i32, &str> = IntervalTree::default();
    /// assert_eq!(tree.entry(0..10).key(), &(0..10));
    /// ```
    #[inline]
    pub fn key(&self) -> &Range<R> {
        match self {
            Entry::Vacant(entry) => entry.key(),
            Entry::Occupied(entry) => entry.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use interavl::IntervalTree;
    ///
    /// let mut tree: IntervalTree<i32, u32> = IntervalTree::default();
    ///
    /// tree.entry(0..10).or_insert(42);
    /// assert_eq!(tree.get(&(0..10)), Some(&42));
    ///
    /// *tree.entry(0..10).or_insert(100) += 1;
    /// assert_eq!(tree.get(&(0..10)), Some(&43));
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use interavl::IntervalTree;
    ///
    /// let mut tree: IntervalTree<i32, String> = IntervalTree::default();
    /// let s = "hello".to_string();
    ///
    /// tree.entry(0..10).or_insert_with(|| s);
    ///
    /// assert_eq!(tree.get(&(0..10)), Some(&"hello".to_string()));
    /// ```
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of
    /// the default function. This method allows for generating key-derived
    /// values for insertion by providing the default function a reference to
    /// the key that was moved during the `.entry(key)` method call.
    ///
    /// # Examples
    ///
    /// ```
    /// use interavl::IntervalTree;
    ///
    /// let mut tree: IntervalTree<i32, i32> = IntervalTree::default();
    ///
    /// tree.entry(0..10).or_insert_with_key(|key| key.start + key.end);
    ///
    /// assert_eq!(tree.get(&(0..10)), Some(&10));
    /// ```
    #[inline]
    pub fn or_insert_with_key<F: FnOnce(&Range<R>) -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use interavl::IntervalTree;
    ///
    /// let mut tree: IntervalTree<i32, u32> = IntervalTree::default();
    ///
    /// tree.entry(0..10)
    ///     .and_modify(|v| *v += 1)
    ///     .or_insert(42);
    /// assert_eq!(tree.get(&(0..10)), Some(&42));
    ///
    /// tree.entry(0..10)
    ///     .and_modify(|v| *v += 1)
    ///     .or_insert(42);
    /// assert_eq!(tree.get(&(0..10)), Some(&43));
    /// ```
    #[inline]
    pub fn and_modify<F: FnOnce(&mut V)>(mut self, f: F) -> Self {
        match &mut self {
            Entry::Occupied(entry) => {
                f(entry.get_mut());
            }
            Entry::Vacant(_) => {}
        }
        self
    }

    /// Sets the value of the entry, and returns an OccupiedEntry.
    ///
    /// # Examples
    ///
    /// ```
    /// use interavl::IntervalTree;
    ///
    /// let mut tree: IntervalTree<i32, &str> = IntervalTree::default();
    /// let entry = tree.entry(0..10).insert_entry("hello");
    ///
    /// assert_eq!(entry.key(), &(0..10));
    /// ```
    #[inline]
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, R, V> {
        match self {
            Entry::Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            Entry::Vacant(entry) => {
                let key = entry.key.clone();
                entry.tree.insert(key.clone(), value);
                OccupiedEntry {
                    key,
                    tree: entry.tree,
                }
            }
        }
    }
}

impl<'a, R, V> Entry<'a, R, V>
where
    R: Ord + Clone + Debug,
    V: Default,
{
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use interavl::IntervalTree;
    ///
    /// let mut tree: IntervalTree<i32, Option<u32>> = IntervalTree::default();
    /// tree.entry(0..10).or_default();
    ///
    /// assert_eq!(tree.get(&(0..10)), Some(&None));
    /// ```
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(V::default()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_entry_or_insert() {
        let mut tree: IntervalTree<i32, i32> = IntervalTree::default();

        // Insert via vacant entry
        tree.entry(0..10).or_insert(42);
        assert_eq!(tree.get(&(0..10)), Some(&42));

        // Entry is now occupied, should not change
        tree.entry(0..10).or_insert(100);
        assert_eq!(tree.get(&(0..10)), Some(&42));
    }

    #[test]
    fn test_entry_or_insert_with() {
        let mut tree: IntervalTree<i32, String> = IntervalTree::default();

        tree.entry(0..10).or_insert_with(|| "hello".to_string());
        assert_eq!(tree.get(&(0..10)), Some(&"hello".to_string()));

        // Should not call the closure again
        tree.entry(0..10).or_insert_with(|| "world".to_string());
        assert_eq!(tree.get(&(0..10)), Some(&"hello".to_string()));
    }

    #[test]
    fn test_entry_or_insert_with_key() {
        let mut tree: IntervalTree<i32, i32> = IntervalTree::default();

        tree.entry(0..10)
            .or_insert_with_key(|key| key.start + key.end);
        assert_eq!(tree.get(&(0..10)), Some(&10));
    }

    #[test]
    fn test_entry_and_modify() {
        let mut tree: IntervalTree<i32, u32> = IntervalTree::default();

        // On vacant, and_modify should not do anything
        tree.entry(0..10).and_modify(|v| *v += 1).or_insert(42);
        assert_eq!(tree.get(&(0..10)), Some(&42));

        // On occupied, and_modify should modify the value
        tree.entry(0..10).and_modify(|v| *v += 1).or_insert(100);
        assert_eq!(tree.get(&(0..10)), Some(&43));
    }

    #[test]
    fn test_entry_insert_entry() {
        let mut tree: IntervalTree<i32, &str> = IntervalTree::default();

        // Insert on vacant
        let entry = tree.entry(0..10).insert_entry("hello");
        assert_eq!(entry.key(), &(0..10));
        assert_eq!(entry.get(), &"hello");

        // Insert on occupied - should replace
        let entry = tree.entry(0..10).insert_entry("world");
        assert_eq!(entry.key(), &(0..10));
        assert_eq!(entry.get(), &"world");
    }

    #[test]
    fn test_entry_or_default() {
        let mut tree: IntervalTree<i32, Option<u32>> = IntervalTree::default();

        tree.entry(0..10).or_default();
        assert_eq!(tree.get(&(0..10)), Some(&None));
    }

    #[test]
    fn test_entry_key() {
        let mut tree: IntervalTree<i32, i32> = IntervalTree::default();

        let entry = tree.entry(0..10);
        assert_eq!(entry.key(), &(0..10));
    }

    #[test]
    fn test_vacant_entry_into_key() {
        let mut tree: IntervalTree<i32, i32> = IntervalTree::default();

        let entry = tree.entry(0..10);
        match entry {
            Entry::Vacant(vacant) => {
                let key = vacant.into_key();
                assert_eq!(key, 0..10);
            }
            Entry::Occupied(_) => panic!("Expected vacant entry"),
        }
    }

    #[test]
    fn test_occupied_entry_remove() {
        let mut tree: IntervalTree<i32, i32> = IntervalTree::default();
        tree.insert(0..10, 42);

        let entry = tree.entry(0..10);
        match entry {
            Entry::Occupied(occupied) => {
                let value = occupied.remove();
                assert_eq!(value, 42);
            }
            Entry::Vacant(_) => panic!("Expected occupied entry"),
        }

        assert!(!tree.contains_key(&(0..10)));
    }

    #[test]
    fn test_occupied_entry_insert() {
        let mut tree: IntervalTree<i32, i32> = IntervalTree::default();
        tree.insert(0..10, 42);

        let entry = tree.entry(0..10);
        match entry {
            Entry::Occupied(mut occupied) => {
                let old = occupied.insert(100);
                assert_eq!(old, 42);
                assert_eq!(occupied.get(), &100);
            }
            Entry::Vacant(_) => panic!("Expected occupied entry"),
        }
    }
}
