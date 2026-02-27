//! Channel operation verification.
//!
//! Generates VCs for channel safety: send-on-closed, bounded capacity overflow,
//! and recv deadlock (empty-and-closed).

use crate::vcgen::{VcKind, VcLocation, VerificationCondition};
use rust_fv_smtlib::script::Script;

/// Channel state information.
#[derive(Debug, Clone)]
pub struct ChannelState {
    /// Channel name/identifier
    pub name: String,
    /// Channel capacity (None = unbounded)
    pub capacity: Option<usize>,
    /// True if channel is closed
    pub is_closed: bool,
}

/// Channel operation type.
#[derive(Debug, Clone)]
pub enum ChannelOp {
    /// Send operation
    Send {
        /// Value being sent (symbolic)
        value: String,
    },
    /// Receive operation
    Recv,
}

/// Generate channel operation verification conditions.
///
/// For Send:
/// - VC 1: Channel not closed at send (VcKind::ChannelSafety)
/// - VC 2 (bounded only): Channel has capacity
/// - Warning (unbounded only): Diagnostic VC noting unbounded channel modeled with limit
///
/// For Recv:
/// - VC: Channel not empty-and-closed (avoid deadlock)
pub fn channel_operation_vcs(
    channel: &ChannelState,
    operation: &ChannelOp,
    location: VcLocation,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    match operation {
        ChannelOp::Send { value: _ } => {
            // VC 1: Channel not closed at send
            let description = format!("Channel {} must not be closed at send", channel.name);
            vcs.push(VerificationCondition {
                description,
                script: Script::new(), // Placeholder
                location: VcLocation {
                    vc_kind: VcKind::ChannelSafety,
                    ..location.clone()
                },
            });

            match channel.capacity {
                Some(cap) => {
                    // VC 2: Channel has capacity
                    let description = format!(
                        "Bounded channel {} has capacity (max {})",
                        channel.name, cap
                    );
                    vcs.push(VerificationCondition {
                        description,
                        script: Script::new(), // Placeholder
                        location: VcLocation {
                            vc_kind: VcKind::ChannelSafety,
                            ..location.clone()
                        },
                    });
                }
                None => {
                    // Warning: Unbounded channel modeled with limit
                    let description = format!(
                        "Unbounded channel {} modeled with verification limit; may miss capacity issues",
                        channel.name
                    );
                    vcs.push(VerificationCondition {
                        description,
                        script: Script::new(), // Placeholder
                        location: VcLocation {
                            vc_kind: VcKind::ChannelSafety,
                            ..location
                        },
                    });
                }
            }
        }
        ChannelOp::Recv => {
            // VC: Channel not empty-and-closed
            let description = format!(
                "Channel {} must have items or be open (avoid deadlock)",
                channel.name
            );
            vcs.push(VerificationCondition {
                description,
                script: Script::new(), // Placeholder
                location: VcLocation {
                    vc_kind: VcKind::ChannelSafety,
                    ..location
                },
            });
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_location() -> VcLocation {
        VcLocation {
            function: "test_fn".to_string(),
            block: 0,
            statement: 0,
            source_file: None,
            source_line: None,
            source_column: None,
            contract_text: None,
            vc_kind: VcKind::ChannelSafety,
        }
    }

    #[test]
    fn test_send_on_closed_channel() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: Some(10),
            is_closed: true,
        };
        let op = ChannelOp::Send {
            value: "x".to_string(),
        };
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        // Should have: 1 closed-check VC + 1 capacity VC
        assert_eq!(vcs.len(), 2);
        assert!(vcs[0].description.contains("must not be closed"));
    }

    #[test]
    fn test_send_on_open_channel() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: Some(10),
            is_closed: false,
        };
        let op = ChannelOp::Send {
            value: "x".to_string(),
        };
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        // Should have: 1 closed-check VC + 1 capacity VC
        assert_eq!(vcs.len(), 2);
        assert!(vcs[0].description.contains("must not be closed"));
    }

    #[test]
    fn test_bounded_send_capacity() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: Some(10),
            is_closed: false,
        };
        let op = ChannelOp::Send {
            value: "x".to_string(),
        };
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        assert_eq!(vcs.len(), 2);
        assert!(vcs[1].description.contains("has capacity"));
        assert!(vcs[1].description.contains("max 10"));
    }

    #[test]
    fn test_unbounded_send_warning() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: None,
            is_closed: false,
        };
        let op = ChannelOp::Send {
            value: "x".to_string(),
        };
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        assert_eq!(vcs.len(), 2);
        assert!(vcs[1].description.contains("Unbounded channel"));
        assert!(
            vcs[1]
                .description
                .contains("modeled with verification limit")
        );
    }

    #[test]
    fn test_recv_deadlock() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: Some(10),
            is_closed: false,
        };
        let op = ChannelOp::Recv;
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        assert_eq!(vcs.len(), 1);
        assert!(vcs[0].description.contains("must have items or be open"));
        assert!(vcs[0].description.contains("avoid deadlock"));
    }

    #[test]
    fn test_recv_open_channel() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: None,
            is_closed: false,
        };
        let op = ChannelOp::Recv;
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        assert_eq!(vcs.len(), 1);
        assert!(vcs[0].description.contains("must have items or be open"));
    }

    #[test]
    fn test_send_generates_two_vcs_bounded() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: Some(5),
            is_closed: false,
        };
        let op = ChannelOp::Send {
            value: "x".to_string(),
        };
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        assert_eq!(vcs.len(), 2);
    }

    #[test]
    fn test_recv_generates_one_vc() {
        let channel = ChannelState {
            name: "ch".to_string(),
            capacity: Some(10),
            is_closed: false,
        };
        let op = ChannelOp::Recv;
        let vcs = channel_operation_vcs(&channel, &op, test_location());
        assert_eq!(vcs.len(), 1);
    }
}
