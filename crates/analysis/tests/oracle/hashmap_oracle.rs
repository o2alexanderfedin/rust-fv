//! Proptest oracle tests for HashMap<K,V> stdlib contracts.
//!
//! Validates that all HashMap contract postconditions from
//! `crates/analysis/src/stdlib_contracts/hashmap.rs` hold for real HashMap operations.

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Oracle for HashMap::insert postconditions:
    /// - self.get(key) == Some(&value) after insert
    /// - other keys unchanged (frame condition)
    /// - len tracking: new key => len + 1, existing key => same len
    /// - result == old(self.get(key))
    #[test]
    fn hashmap_insert_oracle(
        initial in prop::collection::hash_map(any::<String>(), any::<i32>(), 0..20),
        key in any::<String>(),
        value in any::<i32>(),
    ) {
        let mut map = initial.clone();
        let old_len = map.len();
        let had_key = map.contains_key(&key);
        let old_value = map.get(&key).cloned();

        let result = map.insert(key.clone(), value);

        // Postcondition 1: get(key) == Some(&value)
        prop_assert_eq!(map.get(&key), Some(&value));

        // Postcondition 2: frame condition -- other keys unchanged
        for (k, v) in &initial {
            if k != &key {
                prop_assert_eq!(map.get(k), Some(v));
            }
        }

        // Postcondition 3: length tracking
        if had_key {
            prop_assert_eq!(map.len(), old_len);
        } else {
            prop_assert_eq!(map.len(), old_len + 1);
        }

        // Postcondition 4: return value is old mapping
        prop_assert_eq!(result, old_value);
    }

    /// Oracle for HashMap::remove postconditions:
    /// - self.get(key) == None after remove
    /// - other keys unchanged (frame condition)
    /// - len tracking: had key => len - 1, no key => same len
    /// - result == old(self.get(key))
    #[test]
    fn hashmap_remove_oracle(
        initial in prop::collection::hash_map(any::<String>(), any::<i32>(), 0..20),
        key in any::<String>(),
    ) {
        let mut map = initial.clone();
        let old_len = map.len();
        let had_key = map.contains_key(&key);
        let old_value = map.get(&key).cloned();

        let result = map.remove(&key);

        // Postcondition 1: key no longer present
        prop_assert_eq!(map.get(&key), None);

        // Postcondition 2: frame condition
        for (k, v) in &initial {
            if k != &key {
                prop_assert_eq!(map.get(k), Some(v));
            }
        }

        // Postcondition 3: length tracking
        if had_key {
            prop_assert_eq!(map.len(), old_len - 1);
        } else {
            prop_assert_eq!(map.len(), old_len);
        }

        // Postcondition 4: return value
        prop_assert_eq!(result, old_value);
    }

    /// Oracle for HashMap::contains_key postcondition:
    /// - result == self.get(key).is_some()
    #[test]
    fn hashmap_contains_key_oracle(
        map in prop::collection::hash_map(any::<String>(), any::<i32>(), 0..20),
        key in any::<String>(),
    ) {
        let contains = map.contains_key(&key);
        let get_is_some = map.get(&key).is_some();

        // Postcondition: contains_key == get(key).is_some()
        prop_assert_eq!(contains, get_is_some);
    }

    /// Oracle for HashMap::len postcondition:
    /// - len matches actual entry count
    #[test]
    fn hashmap_len_oracle(
        map in prop::collection::hash_map(any::<String>(), any::<i32>(), 0..50),
    ) {
        let result = map.len();

        // Verify len matches iteration count
        let manual_count = map.keys().count();
        prop_assert_eq!(result, manual_count);
    }

    /// Oracle for HashMap::is_empty postcondition:
    /// - result == (self.len() == 0)
    #[test]
    fn hashmap_is_empty_oracle(
        map in prop::collection::hash_map(any::<String>(), any::<i32>(), 0..20),
    ) {
        let result = map.is_empty();

        prop_assert_eq!(result, map.len() == 0);
    }

    /// Oracle for HashMap::clear postconditions:
    /// - self.len() == 0
    /// - forall k: self.get(k) == None
    #[test]
    fn hashmap_clear_oracle(
        initial in prop::collection::hash_map(any::<String>(), any::<i32>(), 0..20),
    ) {
        let mut map = initial.clone();
        let keys: Vec<String> = initial.keys().cloned().collect();

        map.clear();

        // Postcondition 1: len == 0
        prop_assert_eq!(map.len(), 0);

        // Postcondition 2: all old keys map to None
        for k in &keys {
            prop_assert_eq!(map.get(k), None);
        }
    }

    /// Frame condition stress test: insert one key, verify 5 random other keys unchanged.
    #[test]
    fn hashmap_frame_condition_stress(
        initial in prop::collection::hash_map(0..100i32, any::<i32>(), 5..20),
        new_key in 100..200i32,
        value in any::<i32>(),
    ) {
        let mut map = initial.clone();

        // Insert a key guaranteed not in initial (100..200 vs 0..100)
        map.insert(new_key, value);

        // Frame: all original keys unchanged
        for (k, v) in &initial {
            prop_assert_eq!(map.get(k), Some(v));
        }
    }
}
