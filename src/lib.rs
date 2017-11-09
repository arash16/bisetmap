//! A fast and thread-safe two-way hash map of sets. It is best suited where you need to associate
//! two collumns uniquely. Each key is associated to one or more other unique values.
//!
//! A `BisetMap<L, R>` is a Multi-Hash-Map between values of type `L`, called left values, and values
//! of type `R`, called right values. This means every left value is associated with one or more
//! right values and vice versa. Compare this to a [`HashMap`], where every key is associated with
//! exactly one value.
//!
//! The structure is interior mutable and all operations are thread safe. Each clone provides access
//! to the same underlying data.
//!
//! Internally, a `BisetMap` is composed of two `HashMap`s, one for the left-to-right direction and
//! one for right-to-left. As such, the big-O performance of the `get`, `remove`, `insert`, and
//! `contains` methods are the same as those of a `HashMap`.
//!
//! As with `HashMap`, it is considered a logic error to modify a value's hash while it is in the
//! `BisetMap` using a `Cell`, `RefCell`, etc.
//!
//! # Examples
//!
//! ```
//! use bisetmap::BisetMap;
//!
//! let subscriptions = BisetMap::new();
//!
//! // insert client-ids and subscription topics
//! subscriptions.insert("Bob", "Tech");
//! subscriptions.insert("Bob", "Math");
//! subscriptions.insert("Alice", "Tech");
//! subscriptions.insert("Alice", "Romance");
//!
//! // retrieve topic by client-id (left to right)
//! assert_eq!(subscriptions.get(&"Bob"), ["Math", "Tech"]);
//! assert_eq!(subscriptions.get(&"Alice"), ["Romance", "Tech"]);
//!
//! // retrieve clients by topic (right to left)
//! assert_eq!(subscriptions.rev_get(&"Tech"), ["Alice", "Bob"]);
//! assert_eq!(subscriptions.rev_get(&"Math"), ["Bob"]);
//!
//! // check membership
//! assert!(subscriptions.contains(&"Bob", &"Math"));
//! assert!(!subscriptions.contains(&"Bob", &"Romance"));
//!
//! // check key/value existence
//! assert!(subscriptions.key_exists(&"Alice"));
//! assert!(subscriptions.value_exists(&"Tech"));
//! ```
//!
//! ## Insertion and Uniqueness
//!
//! Consider the following example:
//!
//! ```
//! use bisetmap::BisetMap;
//!
//! let bmap = BisetMap::new();
//! bmap.insert('a', 1);
//! bmap.insert('a', 1); // what to do here?
//! ```
//!
//! Duplicate key-value pairs are ignored and inserted only once
//!
//! [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html

use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, Arc};
use std::hash::Hash;
use std::fmt;

/// A two-way map between keys (left) and values (right).
///
/// See the [module-level documentation] for more details and examples.
///
/// [module-level documentation]: index.html
#[derive(Clone)]
pub struct BisetMap<L:Eq+Hash+Clone, R:Eq+Hash+Clone> {
	hh: Arc<Mutex<(HashMap<L, HashSet<R>>, HashMap<R, HashSet<L>>)>>
}


fn insert_item<L:Eq+Hash, R:Eq+Hash>(h: &mut HashMap<L, HashSet<R>>, k: L, v: R) {
	let s = h.entry(k).or_insert_with(HashSet::new);
	s.insert(v);
}

fn remove_item<L:Eq+Hash, R:Eq+Hash>(h: &mut HashMap<L, HashSet<R>>, k: L, v: &R) {
	if let std::collections::hash_map::Entry::Occupied(mut e) = h.entry(k) {
		e.get_mut().remove(v);
		if e.get().is_empty() {
			e.remove_entry();
		}
	}
}

fn get_item<L:Eq+Hash, R:Eq+Hash+Clone>(h: &HashMap<L, HashSet<R>>, k: &L) -> Vec<R> {
	match h.get(k) {
		Some(s) => s.iter().map(Clone::clone).collect(),
		None => vec![]
	}
}

fn remove_items<L:Eq+Hash, R:Eq+Hash+Clone>(h1: &mut HashMap<L, HashSet<R>>, h2: &mut HashMap<R, HashSet<L>>, k: &L) -> Vec<R> {
	match h1.remove(k) {
		Some(s) => {
			let r = s.iter().map(Clone::clone).collect();
			for v in s {
				remove_item(h2, v, k)
			}
			r
		},
		None => vec![]
	}
}

impl<L:Eq+Hash+Clone, R:Eq+Hash+Clone> BisetMap<L, R> {
    /// Creates an empty `BisetMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap: BisetMap<char, u32> = BisetMap::new();
	/// ```
	pub fn new() -> BisetMap<L, R> {
		BisetMap::default()
	}

    /// Creates an empty `BisetMap` with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap: BisetMap<char, u32> = BisetMap::with_capacity(5);
	/// ```
	pub fn with_capacity(capacity: usize) -> BisetMap<L, R> {
		BisetMap {
        	hh: Arc::new(Mutex::new( (HashMap::with_capacity(capacity), HashMap::with_capacity(capacity)) ))
        }
	}

    /// Removes all key-value pairs from the `BisetMap`, but keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('b', 2);
    /// bmap.insert('c', 3);
    /// bmap.clear();
    /// assert!(bmap.len() == 0);
	/// ```
	pub fn clear(&self) {
		let (ref mut h1, ref mut h2) = *self.hh.lock().unwrap();
		h1.clear();
		h2.clear();
	}

    /// Returns a new BisetMap where keys and values are swapped.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('b', 2);
    /// bmap.insert('c', 3);
    /// let rmap = bmap.rev();
    /// assert_eq!(rmap.get(&1), ['a']);
	/// ```
	pub fn rev(&self) -> BisetMap<R, L> {
		let (ref h1, ref h2) = *self.hh.lock().unwrap();
		BisetMap {
        	hh: Arc::new(Mutex::new( (h2.clone(), h1.clone()) ))
        }
	}

    /// Returns a vector of (key,values) pairs, where values itself is a vector.
    /// (Order of all pairs is unknown)
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('a', 2);
    /// bmap.insert('b', 3);
    /// assert_eq!(bmap.collect(), vec![('a',vec![1,2]), ('b',vec![3])]);
	/// ```
	pub fn collect(&self) -> Vec<(L, Vec<R>)> {
		self.hh.lock().unwrap().0
			.iter()
			.map(|(l, r)| (l.clone(), r.iter().map(Clone::clone).collect()))
			.collect()
	}

    /// Returns a vector of (key,value) pairs.
    /// (Order of pairs is unknown)
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('a', 2);
    /// bmap.insert('b', 3);
    /// assert_eq!(bmap.flat_collect(), [('a',1), ('a',2), ('b',3)]);
	/// ```
	pub fn flat_collect(&self) -> Vec<(L, R)> {
		self.hh.lock().unwrap().0
			.iter()
			.flat_map(|(l, rs)| rs.iter().map(move |r| (l.clone(), r.clone())))
			.collect()
	}

    /// Inserts the given key-value pair into the `BisetMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('a', 1);
    /// bmap.insert('a', 2);
    /// bmap.insert('b', 3);
    /// assert_eq!(bmap.flat_collect(), [('a',1), ('a',2), ('b',3)]);
	/// ```
	pub fn insert(&self, k: L, v: R) {
		let (ref mut h1, ref mut h2) = *self.hh.lock().unwrap();
		insert_item(h1, k.clone(), v.clone());
		insert_item(h2, v, k);
	}

    /// Removes the specified key-value pair from the `BisetMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('a', 1);
    /// bmap.insert('a', 2);
    /// bmap.insert('c', 3);
    /// assert_eq!(bmap.len(), 2);
    /// assert_eq!(bmap.rev_len(), 3);
    /// bmap.remove(&'a', &2);
    /// assert_eq!(bmap.len(), 2);
    /// assert_eq!(bmap.rev_len(), 2);
	/// ```
	pub fn remove(&self, k: &L, v: &R) {
		let (ref mut h1, ref mut h2) = *self.hh.lock().unwrap();
		remove_item(h1, k.clone(), &v.clone());
		remove_item(h2, v.clone(), &k.clone());
	}

    /// Returns `true` if the map contains the given key-value pair and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// assert!(bmap.contains(&'a', &1));
    /// assert!(!bmap.contains(&'b', &1));
    /// assert!(!bmap.contains(&'a', &2));
	/// ```
	pub fn contains(&self, k: &L, v: &R) -> bool {
		match self.hh.lock().unwrap().0.get(k) {
			Some(s) => s.contains(v),
			None => false
		}
	}

    /// Returns `true` if the map contains the given key (left) value and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// assert!(bmap.key_exists(&'a'));
    /// assert!(!bmap.key_exists(&'b'));
	/// ```
	pub fn key_exists(&self, k: &L) -> bool {
		self.hh.lock().unwrap().0.contains_key(k)
	}

    /// Returns `true` if the map contains the given value (right) and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// assert!(bmap.value_exists(&1));
    /// assert!(!bmap.value_exists(&2));
	/// ```
	pub fn value_exists(&self, v: &R) -> bool {
		self.hh.lock().unwrap().1.contains_key(v)
	}

    /// Returns a vector of values (right) corresponding to the given key (left).
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// assert_eq!(bmap.get(&'a'), [1]);
    /// assert_eq!(bmap.get(&'z'), []);
	/// ```
	pub fn get(&self, k: &L) -> Vec<R> {
		get_item(&self.hh.lock().unwrap().0, &k)
	}

    /// Returns a vector of keys (left) corresponding to the given value (right).
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// assert_eq!(bmap.rev_get(&1), ['a']);
    /// assert_eq!(bmap.rev_get(&2), []);
	/// ```
	pub fn rev_get(&self, v: &R) -> Vec<L> {
		get_item(&self.hh.lock().unwrap().1, &v)
	}

    /// Removes the specified key and all values associated with it.
    ///
    /// Returns a vector of previous values associated with given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('a', 2);
    /// bmap.insert('c', 3);
    /// assert_eq!(bmap.delete(&'a'), [1, 2]);
    /// assert_eq!(bmap.len(), 1);
	/// ```
	pub fn delete(&self, k: &L) -> Vec<R> {
		let (ref mut h1, ref mut h2) = *self.hh.lock().unwrap();
		remove_items(h1, h2, &k)
	}

    /// Removes the specified key and all values associated with it.
    ///
    /// Returns a vector of previous keys associated with given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('b', 1);
    /// bmap.insert('c', 2);
    /// assert_eq!(bmap.rev_delete(&1), ['a', 'b']);
    /// assert_eq!(bmap.len(), 1);
	/// ```
	pub fn rev_delete(&self, v: &R) -> Vec<L> {
		let (ref mut h1, ref mut h2) = *self.hh.lock().unwrap();
		remove_items(h2, h1, &v)
	}

    /// Returns the number of unique keys (left).
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('b', 2);
    /// bmap.insert('c', 3);
    /// bmap.insert('c', 4);
    /// assert_eq!(bmap.len(), 3);
	/// ```
	pub fn len(&self) -> usize {
		self.hh.lock().unwrap().0.len()
	}

    /// Returns the number of unique values (right).
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// bmap.insert('a', 1);
    /// bmap.insert('b', 2);
    /// bmap.insert('c', 3);
    /// bmap.insert('d', 3);
    /// assert_eq!(bmap.rev_len(), 3);
	/// ```
	pub fn rev_len(&self) -> usize {
		self.hh.lock().unwrap().1.len()
	}

    /// Returns `true` if the map contains no key-value pairs, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bisetmap::BisetMap;
    ///
    /// let bmap = BisetMap::new();
    /// assert!(bmap.is_empty());
    /// bmap.insert('a', 1);
    /// assert!(!bmap.is_empty());
    /// bmap.rev_delete(&1);
    /// assert!(bmap.is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.hh.lock().unwrap().0.is_empty()
	}
}


impl<L: Eq+Hash+Clone, R: Eq+Hash+Clone> Default for BisetMap<L,R> {
    fn default() -> BisetMap<L, R> {
        BisetMap {
        	hh: Arc::new(Mutex::new( (HashMap::default(), HashMap::default()) ))
        }
    }
}

impl<L: Eq+Hash+Clone+fmt::Debug, R: Eq+Hash+Clone+fmt::Debug> fmt::Debug for BisetMap<L, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (left, right)) in self.hh.lock().unwrap().0.iter().enumerate() {
            let comma = if i == 0 { "" } else { ", " };
            write!(f, "{}{:?} => {:?}", comma, left, right)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
	use BisetMap;

	#[test]
	fn test1() {
		let h = BisetMap::new();
		h.insert("sdf", "sdfsd");
		h.insert("sdf", "sdfsd");
    	h.insert("a", "1");
    	h.insert("b", "1");
    	h.insert("c", "2");
    	h.insert("c", "3");
    	h.insert("c", "4");

    	println!("{:?}", h);
    	println!("{:?}", h.rev());
    	println!("{:?}", h.collect());
	}

    #[test]
    fn clone_works_with_same_internal_memory() {
    	let h1 = BisetMap::new();
    	let h2 = h1.clone();
    	h1.insert("hello", "world");
        assert_eq!(h2.get(&"hello"), ["world"]);
    }

    #[test]
    fn test_len_function() {
    	let h = BisetMap::new();
    	assert_eq!(h.len(), 0);
    	assert_eq!(h.rev_len(),0);

    	h.insert("a", "1");
    	h.insert("b", "1");
    	h.insert("c", "2");
    	assert_eq!(h.len(), 3);
    	assert_eq!(h.rev_len(),2);

    	h.rev_delete(&"1");
    	assert_eq!(h.len(), 1);
    	assert_eq!(h.rev_len(),1);
    }

    #[test]
    fn is_empty_after_removal() {
    	let h = BisetMap::new();
        assert!(h.is_empty());

    	h.insert("a", "1");
    	h.insert("b", "1");
    	h.insert("c", "2");
        assert!(!h.is_empty());

        h.rev_delete(&"1");
        h.delete(&"c");
        assert!(h.is_empty());
    }
}
