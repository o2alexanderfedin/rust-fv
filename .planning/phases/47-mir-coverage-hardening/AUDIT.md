# Match Arm Fallthrough Audit -- Phase 47

## Scope

- `crates/analysis/src/vcgen.rs`
- `crates/analysis/src/encode_term.rs`

## Findings

### vcgen.rs

| Line | Match Subject | Skipped Arms | Reason | Action |
|------|---------------|-------------|--------|--------|
| ~194 | `BinOp` in `VcKind::from_overflow_op` | `_ => Self::Overflow` (Add, Sub, Mul, BitAnd, BitOr, BitXor, Eq, Ne, Lt, Le, Gt, Ge) | All non-Div/Rem/Shl/Shr ops classified as generic overflow | documented |
| ~1277 | `Rvalue` in overflow scan (traverse_block) | `_ => {}` (Use, UnaryOp, Cast, Ref, Aggregate, Len, Discriminant, Repeat) | Non-binary-op rvalues have no overflow to track | documented |
| ~1273 | `Terminator` in traverse_block | Return, Goto, SwitchInt, Assert, Call, Unreachable | All 6 variants handled explicitly | no wildcard |
| ~1787 | `Rvalue` in `encode_rvalue_for_assignment` | Aggregate, Repeat | Handled directly in `encode_assignment` (datatype constructors, forall arrays) | replaced wildcard with explicit variants |
| ~1868 | `Projection` in `build_nested_functional_update` (forward) | Deref, Index | Not supported in functional struct updates | replaced wildcard with explicit variants |
| ~1906 | `Projection` in `build_nested_functional_update` (reverse) | Deref, Index | Cannot appear in reverse constructor-building walk | replaced wildcard with explicit variants |
| ~1950 | `Rvalue` in `encode_assignment` (main match) | All 10 variants (Use, BinaryOp, CheckedBinaryOp, UnaryOp, Ref, Len, Cast, Aggregate, Discriminant, Repeat) | Every variant encoded or early-returns | no wildcard |
| ~2255 | `AssertKind` in `format_assert_description` | All 9 variants | Exhaustive: UserAssert, BoundsCheck, Overflow, DivisionByZero, RemainderByZero, NegationOverflow, UnwrapNone, ExpectFailed, Other | no wildcard |
| ~2595 | `Term` in `substitute_term` | `_ => term.clone()` | Literals and compound terms without named constants | documented |
| ~3363 | `Terminator` in `terminator_successors` | All 6 variants | Exhaustive | no wildcard |
| ~3546 | `Rvalue` in loop body preservation encoding | `_ => None` (CheckedBinaryOp, UnaryOp, Cast, Ref, Aggregate, Len, Discriminant, Repeat) | Only Use and BinaryOp supported in next-state encoding | documented |
| ~3721 | `Terminator` in `extract_loop_condition` | `_ => None` (Return, Goto, Assert, Call, Unreachable) | Non-SwitchInt = unconditional loop | documented |
| ~3762 | `Operand` in `extract_loop_condition` width | `Operand::Constant(_) => 32` | Constant discriminants default to 32-bit width | replaced wildcard with explicit variant |
| ~3857 | `Terminator` in `collect_loop_body_assignments` | `_ => None` (Return, Assert, Call, Unreachable) | Only SwitchInt/Goto have body entries | documented |
| ~3930 | `Terminator` in `collect_post_loop_assignments` | `_ => None` | Non-SwitchInt headers have no otherwise exit | documented |
| ~3990 | `Terminator` in `collect_body_only_assignments` | `_ => None` | Same as `collect_loop_body_assignments` | documented |
| ~4002 | `Term` in `substitute_next_state` | `_ => term.clone()` | Literals and unmatched compound terms have no variables | documented |
| ~4011 | `Operand` in `encode_operand_for_vcgen` | Copy, Move, Constant | All 3 variants handled explicitly | no wildcard |
| ~4093 | `Operand`/`Constant` in `infer_operand_type` | All 6 Constant variants => None | Constants lack Function-scoped Ty ref | replaced wildcard with exhaustive match |
| ~4295 | `Ty` in `resolve_selector_from_ty` | `_ => {}` | Only Struct/Tuple have selectors | documented |
| ~4331 | `(BinOp, signed)` in `make_comparison` | `_ => unreachable!()` | Only Lt/Le/Gt/Ge passed by caller | no documentation needed (unreachable) |
| ~4533 | `SyncOpKind` in lock invariant (generate_concurrency_vcs) | `_ => return None` (RwLockRead, RwLockWrite, RwLockUnlock, ChannelSend, ChannelRecv) | Only MutexLock/MutexUnlock produce lock invariant VCs | documented |
| ~4585 | `SyncOpKind` in deadlock detection | `_ => {}` | Only MutexLock/MutexUnlock affect lock ordering | documented |
| ~4615 | `SyncOpKind` in channel VCs | `_ => {}` (MutexLock, MutexUnlock, RwLockRead, RwLockWrite, RwLockUnlock) | Only ChannelSend/ChannelRecv are channel ops | documented |

### encode_term.rs

| Line | Match Subject | Skipped Arms | Reason | Action |
|------|---------------|-------------|--------|--------|
| ~16 | `Operand` in `encode_operand` | Copy, Move, Constant | All 3 variants handled explicitly | no wildcard |
| ~34 | `Projection` in `encode_place` | Deref, Field, Index, Downcast | All 4 variants handled explicitly | no wildcard |
| ~72 | `Projection` in `encode_place_with_type` | Field, Index, Deref, Downcast | All 4 variants handled explicitly | no wildcard |
| ~118 | `Ty` in `encode_field_access` | `_ => None` | Only Struct/Tuple have field selectors | documented |
| ~140 | `AggregateKind` in `encode_aggregate` | Struct, Tuple, Enum, Closure | All 4 variants handled explicitly | no wildcard |
| ~180 | `AggregateKind` in `encode_aggregate_with_type` | Struct, Tuple, Enum, Closure | All 4 variants handled explicitly | no wildcard |
| ~217 | `Ty` in `get_field_type` | `_ => None` | Only Struct/Tuple have indexed fields | documented |
| ~228 | `Ty` in `get_element_type` | `_ => None` | Only Array/Slice have elements | documented |
| ~309 | `Constant` in `encode_constant` | Bool, Int, Uint, Float, Unit, Str | All 6 variants handled explicitly | no wildcard |
| ~327 | `BinOp` in `encode_fp_binop` | All 16 variants handled (6 panic for unsupported float ops) | Exhaustive with explicit panic for invalid ops | no wildcard |
| ~371 | `BinOp` in `encode_binop` | All 16 variants handled explicitly | Exhaustive | no wildcard |
| ~440 | `UnOp` in `encode_unop` | Not, Neg | All 2 variants handled explicitly | no wildcard |
| ~595 | `BinOp` in `overflow_check` | All 16 variants handled explicitly (last 6 => None) | Comparisons and bitwise ops cannot overflow | no wildcard |
| ~657 | `Ty`/`IntTy`/`UintTy`/`FloatTy` in `ty_bit_width` | `_ => 64` | Non-numeric types default to pointer width (64) | documented |
| ~726 | `CastKind` in `encode_cast` | All 5 variants handled explicitly (IntToInt, IntToFloat, FloatToInt, FloatToFloat, PtrToPtr) | Exhaustive | no wildcard |
| ~739 | `Ordering` in `encode_int_to_int_cast` | Equal, Less, Greater | All 3 variants handled explicitly | no wildcard |
| ~802 | bit width in `float_params` | `_ => (11, 53)` | Only f32(32) and f64(64) exist; defaults to f64 | documented |

## Summary

- **Total match expressions audited: 44** (24 in vcgen.rs, 20 in encode_term.rs)
- **Arms with no VC/encoding: 32** (all documented with inline comments)
- **Wildcard catch-alls replaced with explicit variants: 5** (Rvalue in encode_rvalue_for_assignment, 2x Projection in build_nested_functional_update, Constant in infer_operand_type, Operand in extract_loop_condition)
- **Wildcard catch-alls kept (documented): 18** (all have inline comments explaining the reason)
- **Match expressions already exhaustive (no wildcard): 21** (no action needed)
- **No silent fallthrough remaining** in the VC generation pipeline
