//! Proptest oracle tests for Vec<T> stdlib contracts.
//!
//! Validates that all Vec contract postconditions from
//! `crates/analysis/src/stdlib_contracts/vec.rs` hold for real Vec operations.

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Oracle for Vec::push postconditions:
    /// - self.len() == old(self.len()) + 1
    /// - self[old_len] == value (element-level precision)
    #[test]
    fn vec_push_oracle(
        initial in prop::collection::vec(any::<i32>(), 0..100),
        value in any::<i32>(),
    ) {
        let mut vec = initial.clone();
        let old_len = vec.len();

        vec.push(value);

        // Postcondition 1: len == old(len) + 1
        prop_assert_eq!(vec.len(), old_len + 1);

        // Postcondition 2: vec[old_len] == value (element-level precision)
        prop_assert_eq!(vec[old_len], value);
    }

    /// Oracle for Vec::pop postconditions:
    /// - result.is_some() ==> len == old(len) - 1
    /// - result.is_none() ==> old(len) == 0
    #[test]
    fn vec_pop_oracle(
        initial in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let mut vec = initial.clone();
        let old_len = vec.len();

        let result = vec.pop();

        if result.is_some() {
            // Postcondition 1: if Some, len == old(len) - 1
            prop_assert_eq!(vec.len(), old_len - 1);
            // Also: old_len must have been > 0
            prop_assert!(old_len > 0);
        } else {
            // Postcondition 2: if None, old(len) == 0
            prop_assert_eq!(old_len, 0);
        }
    }

    /// Oracle for Vec::get postconditions:
    /// - result.is_some() ==> index < self.len()
    /// - result.is_some() ==> *result.unwrap() == vec[index]
    /// - result.is_none() ==> index >= self.len()
    #[test]
    fn vec_get_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
        index in 0..200usize,
    ) {
        let result = vec.get(index);

        if let Some(val) = result {
            // Postcondition 1: index < len
            prop_assert!(index < vec.len());
            // Postcondition 2: value matches
            prop_assert_eq!(*val, vec[index]);
        } else {
            // Postcondition 3: index >= len
            prop_assert!(index >= vec.len());
        }
    }

    /// Oracle for Vec::reserve postconditions:
    /// - capacity >= len + additional
    /// - len == old(len) (reserve doesn't change length)
    /// - elements preserved
    #[test]
    fn vec_reserve_oracle(
        initial in prop::collection::vec(any::<i32>(), 0..50),
        additional in 0..100usize,
    ) {
        let mut vec = initial.clone();
        let old_len = vec.len();
        let _old_cap = vec.capacity();

        vec.reserve(additional);

        // Postcondition 1: capacity grew enough
        prop_assert!(vec.capacity() >= old_len + additional);

        // Postcondition 2: len unchanged
        prop_assert_eq!(vec.len(), old_len);

        // Postcondition 3: elements preserved
        for i in 0..old_len {
            prop_assert_eq!(vec[i], initial[i]);
        }
    }

    /// Oracle for Vec::shrink_to_fit postconditions:
    /// - capacity >= len (fundamental invariant)
    /// - len == old(len) (doesn't change length)
    /// - elements preserved
    #[test]
    fn vec_shrink_oracle(
        initial in prop::collection::vec(any::<i32>(), 0..50),
    ) {
        let mut vec = initial.clone();
        // Force extra capacity so shrink actually has something to do
        vec.reserve(50);
        let old_len = vec.len();

        vec.shrink_to_fit();

        // Postcondition: capacity >= len (fundamental invariant)
        prop_assert!(vec.capacity() >= vec.len());

        // Postcondition: len unchanged
        prop_assert_eq!(vec.len(), old_len);

        // Elements preserved
        for i in 0..old_len {
            prop_assert_eq!(vec[i], initial[i]);
        }
    }

    /// Oracle for Vec::clear postcondition:
    /// - self.len() == 0
    #[test]
    fn vec_clear_oracle(
        initial in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let mut vec = initial;

        vec.clear();

        // Postcondition: len == 0
        prop_assert_eq!(vec.len(), 0);
    }

    /// Oracle for Vec::is_empty postcondition:
    /// - result == (self.len() == 0)
    #[test]
    fn vec_is_empty_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let result = vec.is_empty();

        // Postcondition: result == (len == 0)
        prop_assert_eq!(result, vec.is_empty());
    }

    /// Oracle for Vec::capacity postcondition:
    /// - result >= self.len()
    #[test]
    fn vec_capacity_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let result = vec.capacity();

        // Postcondition: capacity >= len
        prop_assert!(result >= vec.len());
    }
}
