//! Proptest oracle tests for Iterator stdlib contracts.
//!
//! Validates that all Iterator contract postconditions from
//! `crates/analysis/src/stdlib_contracts/iterator.rs` hold for real iterator operations.
//!
//! NOTE: Some clippy lints are suppressed because these oracle tests
//! intentionally exercise iterator operations in ways that mirror the
//! contract specifications rather than idiomatic Rust.

use std::cmp::min;

use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Oracle for Iterator::map length preservation:
    /// - vec.iter().map(f).count() == vec.len()
    #[test]
    fn iter_map_length_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let f = |x: &i32| x.wrapping_mul(2);
        let mapped_count = vec.iter().map(f).count();

        // Postcondition: map preserves length
        prop_assert_eq!(mapped_count, vec.len());
    }

    /// Oracle for Iterator::filter length bound:
    /// - vec.iter().filter(p).count() <= vec.len()
    #[test]
    fn iter_filter_length_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
        threshold in any::<i32>(),
    ) {
        let filtered_count = vec.iter().filter(|&&x| x > threshold).count();

        // Postcondition: filter reduces or maintains length
        prop_assert!(filtered_count <= vec.len());
    }

    /// Oracle for Iterator::take length:
    /// - vec.iter().take(n).count() == min(n, vec.len())
    #[test]
    fn iter_take_length_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
        n in 0..200usize,
    ) {
        let taken_count = vec.iter().take(n).count();

        // Postcondition: take(n) produces min(n, len) elements
        prop_assert_eq!(taken_count, min(n, vec.len()));
    }

    /// Oracle for Iterator::zip length:
    /// - a.iter().zip(b.iter()).count() == min(a.len(), b.len())
    #[test]
    fn iter_zip_length_oracle(
        a in prop::collection::vec(any::<i32>(), 0..100),
        b in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let zipped_count = a.iter().zip(b.iter()).count();

        // Postcondition: zip produces min(a.len(), b.len()) pairs
        prop_assert_eq!(zipped_count, min(a.len(), b.len()));
    }

    /// Oracle for Iterator::enumerate:
    /// - enumerate produces (index, value) pairs with correct indices
    /// - enumerate preserves length
    #[test]
    fn iter_enumerate_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let enumerated: Vec<(usize, &i32)> = vec.iter().enumerate().collect();

        // Postcondition: length preserved
        prop_assert_eq!(enumerated.len(), vec.len());

        // Postcondition: correct (index, value) pairs
        for (i, (idx, val)) in enumerated.iter().enumerate() {
            prop_assert_eq!(*idx, i);
            prop_assert_eq!(*val, &vec[i]);
        }
    }

    /// Oracle for Iterator chain composition:
    /// - map(f).filter(p).collect::<Vec<_>>().len() <= original.len()
    #[test]
    fn iter_chain_composition_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
        threshold in any::<i32>(),
    ) {
        let result: Vec<i32> = vec.iter()
            .map(|x| x.wrapping_mul(2))
            .filter(|&x| x > threshold)
            .collect();

        // Postcondition: filter after map can only reduce length
        prop_assert!(result.len() <= vec.len());
    }

    /// Oracle for Iterator::fold:
    /// - fold produces correct result for simple sum operation
    #[test]
    fn iter_fold_oracle(
        vec in prop::collection::vec(0..100i32, 0..50),
        init in 0..1000i32,
    ) {
        let fold_result = vec.iter().fold(init, |acc, &x| acc.wrapping_add(x));

        // Manual computation
        let mut expected = init;
        for &x in &vec {
            expected = expected.wrapping_add(x);
        }

        prop_assert_eq!(fold_result, expected);
    }

    /// Oracle for Iterator::any / Iterator::all:
    /// - any matches manual check (exists)
    /// - all matches manual check (forall)
    #[test]
    fn iter_any_all_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
        threshold in any::<i32>(),
    ) {
        let any_result = vec.iter().any(|&x| x > threshold);
        let all_result = vec.iter().all(|&x| x > threshold);

        // Manual check for any (exists)
        let manual_any = vec.iter().filter(|&&x| x > threshold).count() > 0;
        prop_assert_eq!(any_result, manual_any);

        // Manual check for all (forall)
        let manual_all = vec.iter().filter(|&&x| !(x > threshold)).count() == 0;
        prop_assert_eq!(all_result, manual_all);
    }

    /// Oracle for Iterator::count:
    /// - vec.iter().count() == vec.len()
    #[test]
    fn iter_count_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let count_result = vec.iter().count();

        prop_assert_eq!(count_result, vec.len());
    }

    /// Oracle for Iterator::collect length:
    /// - collecting an iterator into Vec preserves length
    #[test]
    fn iter_collect_length_oracle(
        vec in prop::collection::vec(any::<i32>(), 0..100),
    ) {
        let collected: Vec<&i32> = vec.iter().collect();

        // Postcondition: collect preserves length
        prop_assert_eq!(collected.len(), vec.len());
    }
}
