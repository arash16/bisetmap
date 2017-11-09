[![crates.io](https://img.shields.io/crates/v/bisetmap.svg)](https://crates.io/crates/bisetmap)
[![Documentation](https://docs.rs/bisetmap/badge.svg)](https://docs.rs/bisetmap/)

# BisetMap
BisetMap is a fast and thread-safe two-way hash map of sets for Rust. It is best suited where you need to associate
two collumns uniquely. Each key is associated to one or more other unique values.

The structure is interior mutable and all operations are thread safe. Each clone provides access to the same
underlying data.

## Usage
To use BisetMap in your Rust project, add `bisetmap = 0.1` to the dependencies section of your `Cargo.toml`.
See [the docs](https://docs.rs/bisetmap/) for more details and example code.

## Examples

```
use bisetmap::BisetMap;

let subscriptions = BisetMap::new();

// insert client-ids and subscription topics
subscriptions.insert("Bob", "Tech");
subscriptions.insert("Bob", "Math");
subscriptions.insert("Alice", "Tech");
subscriptions.insert("Alice", "Romance");

// retrieve topic by client-id (left to right)
assert_eq!(subscriptions.get(&"Bob"), ["Math", "Tech"]);
assert_eq!(subscriptions.get(&"Alice"), ["Romance", "Tech"]);

// retrieve clients by topic (right to left)
assert_eq!(subscriptions.rev_get(&"Tech"), ["Alice", "Bob"]);
assert_eq!(subscriptions.rev_get(&"Math"), ["Bob"]);

// check membership
assert!(subscriptions.contains(&"Bob", &"Math"));
assert!(!subscriptions.contains(&"Bob", &"Romance"));

// check key/value existence
assert!(subscriptions.key_exists(&"Alice"));
assert!(subscriptions.value_exists(&"Tech"));
```

## License
BisetMap is licensed under the MIT license.

