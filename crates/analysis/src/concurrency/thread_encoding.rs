/// Thread interleaving enumeration for bounded concurrency verification.
///
/// This module provides bounded model checking of concurrent programs by
/// enumerating all possible thread interleavings up to a specified number
/// of context switches.
///
/// **Approach:** Lazy recursive enumeration (Pattern 1 from RESEARCH.md).
///
/// - Enumerate interleavings on-demand
/// - Prune branches that exceed context switch bound
/// - Generate minimal interleavings first (fewer switches)
///
/// State of a single thread in the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThreadState {
    /// Thread identifier (0, 1, 2, ...)
    pub thread_id: usize,
    /// Number of execution steps this thread will take
    pub num_steps: usize,
    /// Whether this thread has been spawned (false for main thread)
    pub is_spawned: bool,
}

/// A single event in an interleaving (one thread step).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterleavingEvent {
    /// Which thread executed this step
    pub thread_id: usize,
    /// Step number within that thread (0-based)
    pub step: usize,
    /// Human-readable description of the operation (for debugging)
    pub operation: String,
}

/// A complete interleaving of thread executions.
#[derive(Debug, Clone)]
pub struct Interleaving {
    /// Sequence of events in execution order
    pub events: Vec<InterleavingEvent>,
    /// Total number of context switches in this interleaving
    pub context_switches: usize,
}

/// Internal state for interleaving enumeration.
#[derive(Debug, Clone)]
struct InterleavingState {
    /// Program counter for each thread (how many steps executed)
    thread_pcs: Vec<usize>,
    /// Which thread executed the last step (None if no steps yet)
    last_thread: Option<usize>,
    /// Number of context switches so far
    context_switches: usize,
}

impl InterleavingState {
    /// Returns true if all threads have completed their steps.
    fn all_threads_done(&self, threads: &[ThreadState]) -> bool {
        self.thread_pcs
            .iter()
            .zip(threads.iter())
            .all(|(&pc, thread)| pc >= thread.num_steps)
    }

    /// Returns true if the given thread can be scheduled.
    fn can_schedule(&self, thread_id: usize, threads: &[ThreadState]) -> bool {
        self.thread_pcs[thread_id] < threads[thread_id].num_steps
    }

    /// Execute one step of the given thread, returning updated state.
    fn step(&self, thread_id: usize, threads: &[ThreadState]) -> Option<InterleavingState> {
        if !self.can_schedule(thread_id, threads) {
            return None;
        }

        let mut new_state = self.clone();
        new_state.thread_pcs[thread_id] += 1;

        // Context switch if we're changing threads (after at least one step)
        if let Some(last) = self.last_thread
            && last != thread_id
        {
            new_state.context_switches += 1;
        }
        new_state.last_thread = Some(thread_id);

        Some(new_state)
    }
}

/// Enumerate all possible thread interleavings up to max_switches.
///
/// Uses recursive enumeration with early pruning:
/// - Explores interleavings in order of increasing context switches
/// - Prunes branches exceeding max_switches
/// - Returns empty interleaving if no threads provided
///
/// # Arguments
/// * `threads` - Array of thread states to interleave
/// * `max_switches` - Maximum number of context switches to explore
///
/// # Returns
/// Vector of all valid interleavings within the switch bound.
pub fn enumerate_interleavings(threads: &[ThreadState], max_switches: usize) -> Vec<Interleaving> {
    if threads.is_empty() {
        // Empty threads => single empty interleaving
        return vec![Interleaving {
            events: vec![],
            context_switches: 0,
        }];
    }

    // Start enumeration with all threads at step 0
    // Note: We explore all possible starting threads to get complete coverage,
    // but for sequential execution (max_switches=0), starting thread matters
    let initial_state = InterleavingState {
        thread_pcs: vec![0; threads.len()],
        last_thread: None,
        context_switches: 0,
    };

    let mut results = Vec::new();
    enumerate_recursive(threads, max_switches, initial_state, vec![], &mut results);

    // Remove duplicates (same event sequences)
    // For now, keep all - deduplication can be added later if needed
    results
}

/// Recursive helper for interleaving enumeration.
fn enumerate_recursive(
    threads: &[ThreadState],
    max_switches: usize,
    state: InterleavingState,
    events: Vec<InterleavingEvent>,
    results: &mut Vec<Interleaving>,
) {
    // Base case: all threads done
    if state.all_threads_done(threads) {
        results.push(Interleaving {
            events,
            context_switches: state.context_switches,
        });
        return;
    }

    // Try scheduling each thread
    for thread_id in 0..threads.len() {
        if !state.can_schedule(thread_id, threads) {
            continue;
        }

        // Calculate switch cost
        let switch_cost = match state.last_thread {
            None => 0,                            // First step, no switch
            Some(last) if last == thread_id => 0, // Same thread, no switch
            Some(_) => 1,                         // Different thread, counts as switch
        };

        // Prune if exceeds bound
        if state.context_switches + switch_cost > max_switches {
            continue;
        }

        // Step this thread
        if let Some(new_state) = state.step(thread_id, threads) {
            let mut new_events = events.clone();
            new_events.push(InterleavingEvent {
                thread_id,
                step: state.thread_pcs[thread_id],
                operation: format!("T{}_S{}", thread_id, state.thread_pcs[thread_id]),
            });

            enumerate_recursive(threads, max_switches, new_state, new_events, results);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_enumerate_single_thread() {
        let threads = vec![ThreadState {
            thread_id: 0,
            num_steps: 2,
            is_spawned: false,
        }];
        let interleavings = enumerate_interleavings(&threads, 5);

        // Single thread => exactly 1 interleaving, 0 switches
        assert_eq!(interleavings.len(), 1);
        assert_eq!(interleavings[0].context_switches, 0);
        assert_eq!(interleavings[0].events.len(), 2);
        assert_eq!(interleavings[0].events[0].thread_id, 0);
        assert_eq!(interleavings[0].events[1].thread_id, 0);
    }

    #[test]
    fn test_enumerate_two_threads_zero_switches() {
        let threads = vec![
            ThreadState {
                thread_id: 0,
                num_steps: 2,
                is_spawned: false,
            },
            ThreadState {
                thread_id: 1,
                num_steps: 2,
                is_spawned: true,
            },
        ];
        let interleavings = enumerate_interleavings(&threads, 0);

        // max_switches=0 with 2 threads => impossible to complete both threads
        // (switching from T0 to T1 or vice versa would require 1 switch)
        // So we get 0 complete interleavings
        assert_eq!(interleavings.len(), 0);
    }

    #[test]
    fn test_enumerate_two_threads_one_switch() {
        let threads = vec![
            ThreadState {
                thread_id: 0,
                num_steps: 1,
                is_spawned: false,
            },
            ThreadState {
                thread_id: 1,
                num_steps: 1,
                is_spawned: true,
            },
        ];
        let interleavings = enumerate_interleavings(&threads, 1);

        // 1 step each, max 1 switch => 2 interleavings (0-then-1, 1-then-0)
        assert_eq!(interleavings.len(), 2);

        // Both should have exactly 1 context switch
        for interleaving in &interleavings {
            assert_eq!(interleaving.context_switches, 1);
            assert_eq!(interleaving.events.len(), 2);
        }
    }

    #[test]
    fn test_enumerate_two_threads_two_steps_one_switch() {
        let threads = vec![
            ThreadState {
                thread_id: 0,
                num_steps: 2,
                is_spawned: false,
            },
            ThreadState {
                thread_id: 1,
                num_steps: 2,
                is_spawned: true,
            },
        ];
        let interleavings = enumerate_interleavings(&threads, 1);

        // With 1 switch allowed, we get more interleavings but not all
        assert!(interleavings.len() > 1);

        // All should have <= 1 context switch
        for interleaving in &interleavings {
            assert!(interleaving.context_switches <= 1);
            assert_eq!(interleaving.events.len(), 4);
        }
    }

    #[test]
    fn test_enumerate_respects_max_switches() {
        let threads = vec![
            ThreadState {
                thread_id: 0,
                num_steps: 2,
                is_spawned: false,
            },
            ThreadState {
                thread_id: 1,
                num_steps: 2,
                is_spawned: true,
            },
        ];

        let interleavings_0 = enumerate_interleavings(&threads, 0);
        let interleavings_1 = enumerate_interleavings(&threads, 1);
        let interleavings_2 = enumerate_interleavings(&threads, 2);

        // More switches => more interleavings
        assert!(interleavings_1.len() > interleavings_0.len());
        assert!(interleavings_2.len() > interleavings_1.len());
    }

    #[test]
    fn test_interleaving_event_fields() {
        let event = InterleavingEvent {
            thread_id: 1,
            step: 3,
            operation: "load x".to_string(),
        };

        assert_eq!(event.thread_id, 1);
        assert_eq!(event.step, 3);
        assert_eq!(event.operation, "load x");
    }

    #[test]
    fn test_empty_threads() {
        let threads: Vec<ThreadState> = vec![];
        let interleavings = enumerate_interleavings(&threads, 5);

        // 0 threads => 1 interleaving (empty)
        assert_eq!(interleavings.len(), 1);
        assert_eq!(interleavings[0].events.len(), 0);
        assert_eq!(interleavings[0].context_switches, 0);
    }

    #[test]
    fn test_three_threads_bounded() {
        let threads = vec![
            ThreadState {
                thread_id: 0,
                num_steps: 1,
                is_spawned: false,
            },
            ThreadState {
                thread_id: 1,
                num_steps: 1,
                is_spawned: true,
            },
            ThreadState {
                thread_id: 2,
                num_steps: 1,
                is_spawned: true,
            },
        ];
        let interleavings = enumerate_interleavings(&threads, 2);

        // 3 threads, 1 step each, max 2 switches => should enumerate all 6 orderings
        assert_eq!(interleavings.len(), 6);

        // All should have 2 context switches (3 threads => 2 switches minimum)
        for interleaving in &interleavings {
            assert_eq!(interleaving.context_switches, 2);
            assert_eq!(interleaving.events.len(), 3);
        }
    }
}
