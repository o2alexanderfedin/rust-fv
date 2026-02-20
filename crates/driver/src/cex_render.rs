//! Typed SMT value rendering for counterexample output.
//!
//! Transforms raw SMT model pairs (e.g., `("_1", "#x00000005")`) into
//! human-readable, Rust-typed counterexample values (e.g., `"i32: 5"`).
//!
//! This module is the single rendering engine used by both ariadne terminal
//! output (Plan 03) and JSON output (Plan 04).

use std::collections::HashMap;

use rust_fv_analysis::ir::{self, IntTy, Mutability, Ty, UintTy};
use serde_json::Value as JsonValue;

// ============================================================================
// Public API Types
// ============================================================================

/// A rendered counterexample value with both a human-readable display string
/// and a structured JSON value for machine consumption.
#[derive(Debug, Clone, PartialEq)]
pub struct CexValue {
    /// Human-readable display string (e.g., `"i32: 5"`, `"bool: true"`).
    pub display: String,
    /// Structured JSON representation (e.g., `5`, `true`, `{"x":3,"y":-1}`).
    pub raw: JsonValue,
}

/// A single variable in a counterexample with its Rust-typed rendering.
#[derive(Debug, Clone, PartialEq)]
pub struct CexVariable {
    /// Source-level variable name (translated from SSA, e.g., `"x"` not `"_1"`).
    pub name: String,
    /// Rust type name string (e.g., `"i32"`, `"bool"`, `"Point"`).
    pub ty: String,
    /// Final rendered display string (same as `at_failure.display` if SSA versions exist).
    pub display: String,
    /// Structured JSON representation.
    pub raw: JsonValue,
    /// Initial value for SSA multi-version variables (e.g., `x_0` before reassignment).
    pub initial: Option<CexValue>,
    /// Value at point of failure for SSA multi-version variables.
    pub at_failure: Option<CexValue>,
}

// ============================================================================
// Public API Functions
// ============================================================================

/// Render raw SMT model pairs into typed, human-readable counterexample variables.
///
/// # Arguments
/// * `model` - Raw `(ssa_name, smt_value)` pairs from Z3 model output.
/// * `source_names` - Map from SSA name (e.g., `"_1"`) to source name (e.g., `"x"`).
/// * `locals` - Typed local variables for type-dispatch rendering.
/// * `params` - Typed function parameters for type-dispatch rendering.
///
/// # Returns
/// Rendered variables with human-readable display values.
/// Ghost variables (where `is_ghost == true`) are excluded.
pub fn render_counterexample(
    model: &[(String, String)],
    source_names: &HashMap<String, String>,
    locals: &[ir::Local],
    params: &[ir::Local],
) -> Vec<CexVariable> {
    // Build lookup map from SSA name to ir::Local for type dispatch
    let local_map: HashMap<&str, &ir::Local> = locals
        .iter()
        .chain(params.iter())
        .filter(|l| !l.is_ghost)
        .map(|l| (l.name.as_str(), l))
        .collect();

    // Build reverse map: source name -> all SSA names for SSA multi-version detection
    // We need to detect when both _init and _N variants of the same source var exist
    let mut source_to_ssa: HashMap<String, Vec<String>> = HashMap::new();
    for (ssa_name, _) in model {
        let src = source_names
            .get(ssa_name)
            .cloned()
            .unwrap_or_else(|| ssa_name.clone());
        source_to_ssa.entry(src).or_default().push(ssa_name.clone());
    }

    // Collect model pairs into a lookup for fast access
    let model_map: HashMap<&str, &str> = model
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();

    // Track which SSA names we've already processed (to avoid duplicates from SSA grouping)
    let mut processed: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut result: Vec<CexVariable> = Vec::new();

    for (ssa_name, smt_value) in model {
        if processed.contains(ssa_name) {
            continue;
        }

        // Skip if the local is ghost
        let local = match local_map.get(ssa_name.as_str()) {
            Some(l) => *l,
            None => {
                // Variable not found in locals/params — skip (could be internal SSA var)
                // But check if there's a source name that maps to a known local
                if let Some(src) = source_names.get(ssa_name) {
                    // Try to find a local with the source name matching
                    let found = locals
                        .iter()
                        .chain(params.iter())
                        .find(|l| !l.is_ghost && &l.name == ssa_name);
                    if found.is_none() {
                        processed.insert(ssa_name.clone());
                        // We still render it if we can guess the type from other SSA vars
                        // For simplicity, skip unknown locals
                        let _ = src;
                        continue;
                    }
                    found.unwrap()
                } else {
                    processed.insert(ssa_name.clone());
                    continue;
                }
            }
        };

        // Determine the source-level name
        let src_name = source_names
            .get(ssa_name)
            .cloned()
            .unwrap_or_else(|| ssa_name.clone());

        // Check for SSA multi-version siblings
        let siblings = source_to_ssa.get(&src_name).cloned().unwrap_or_default();
        let has_init_version = siblings.len() > 1
            && siblings
                .iter()
                .any(|s| s.ends_with("_init") || s.ends_with("_0"));
        let has_failure_version = siblings.len() > 1
            && siblings
                .iter()
                .any(|s| s.ends_with("_1") || s.ends_with("_final"));

        // Mark all siblings as processed
        for sibling in &siblings {
            processed.insert(sibling.clone());
        }

        let ty_name = ty_name_string(&local.ty);

        if has_init_version && has_failure_version && siblings.len() >= 2 {
            // SSA multi-version: find initial and final values
            let init_ssa = siblings
                .iter()
                .find(|s| s.ends_with("_init") || s.ends_with("_0"))
                .cloned()
                .unwrap_or_else(|| ssa_name.clone());
            let fail_ssa = siblings
                .iter()
                .find(|s| s.ends_with("_1") || s.ends_with("_final"))
                .cloned()
                .unwrap_or_else(|| ssa_name.clone());

            let init_val = model_map
                .get(init_ssa.as_str())
                .copied()
                .unwrap_or(smt_value);
            let fail_val = model_map
                .get(fail_ssa.as_str())
                .copied()
                .unwrap_or(smt_value);

            let initial_cv = render_typed_value(init_val, &local.ty);
            let failure_cv = render_typed_value(fail_val, &local.ty);

            result.push(CexVariable {
                name: src_name,
                ty: ty_name,
                display: failure_cv.display.clone(),
                raw: failure_cv.raw.clone(),
                initial: Some(initial_cv),
                at_failure: Some(failure_cv),
            });
        } else {
            // Single version
            let cv = render_typed_value(smt_value, &local.ty);
            result.push(CexVariable {
                name: src_name,
                ty: ty_name,
                display: cv.display.clone(),
                raw: cv.raw.clone(),
                initial: None,
                at_failure: None,
            });
        }
    }

    result
}

/// Render a single SMT value using the given Rust type for formatting dispatch.
///
/// This is the core rendering function dispatching on type variant.
pub fn render_typed_value(smt_val: &str, ty: &Ty) -> CexValue {
    match ty {
        Ty::Int(int_ty) => render_int(smt_val, *int_ty),
        Ty::Uint(uint_ty) => render_uint(smt_val, *uint_ty),
        Ty::Bool => render_bool(smt_val),
        Ty::Struct(name, fields) => render_struct(smt_val, name, fields),
        Ty::Enum(name, variants) => render_enum(smt_val, name, variants),
        Ty::RawPtr(inner, _) | Ty::Ref(inner, _) => render_ptr(smt_val, inner),
        Ty::Array(elem_ty, _) | Ty::Slice(elem_ty) => render_array(smt_val, elem_ty),
        Ty::Tuple(fields) => render_tuple(smt_val, fields),
        // Fall back to raw string for unhandled types
        _ => CexValue {
            display: smt_val.to_string(),
            raw: JsonValue::String(smt_val.to_string()),
        },
    }
}

// ============================================================================
// Private Rendering Helpers
// ============================================================================

/// Parse a Z3 bitvector string to a raw bit pattern as u128.
///
/// Handles `#xHEXSTRING` and `#bBINSTRING` formats.
/// Returns `None` if the string is not a bitvector or parsing fails.
fn parse_bitvec(s: &str) -> Option<u128> {
    if let Some(hex_str) = s.strip_prefix("#x") {
        if hex_str.is_empty() {
            return None;
        }
        u128::from_str_radix(hex_str, 16).ok()
    } else if let Some(bin_str) = s.strip_prefix("#b") {
        if bin_str.is_empty() {
            return None;
        }
        u128::from_str_radix(bin_str, 2).ok()
    } else {
        None
    }
}

/// Proper two's complement reinterpretation.
fn bitvec_to_signed(bits: u128, width: u32) -> i128 {
    if width == 0 {
        return 0;
    }
    if width >= 128 {
        return bits as i128;
    }
    let mask = (1u128 << width).wrapping_sub(1);
    let truncated = bits & mask;
    let sign_bit = 1u128 << (width - 1);
    if truncated & sign_bit != 0 {
        // Negative value: truncated - 2^width
        truncated as i128 - (1i128 << width)
    } else {
        truncated as i128
    }
}

/// Render a signed integer from an SMT value string.
fn render_int(smt_val: &str, int_ty: IntTy) -> CexValue {
    let type_prefix = match int_ty {
        IntTy::I8 => "i8",
        IntTy::I16 => "i16",
        IntTy::I32 => "i32",
        IntTy::I64 => "i64",
        IntTy::I128 => "i128",
        IntTy::Isize => "isize",
    };
    let width = int_ty.bit_width();

    if let Some(bits) = parse_bitvec(smt_val) {
        let signed_val = bitvec_to_signed(bits, width);
        // serde_json::Number supports i64 but not i128; clamp for display purposes
        let raw_num = if signed_val >= i64::MIN as i128 && signed_val <= i64::MAX as i128 {
            JsonValue::Number(serde_json::Number::from(signed_val as i64))
        } else {
            JsonValue::String(signed_val.to_string())
        };
        CexValue {
            display: format!("{}: {}", type_prefix, signed_val),
            raw: raw_num,
        }
    } else if let Ok(n) = smt_val.parse::<i64>() {
        // Plain decimal integer from Z3
        CexValue {
            display: format!("{}: {}", type_prefix, n),
            raw: JsonValue::Number(serde_json::Number::from(n)),
        }
    } else {
        // Fallback
        CexValue {
            display: format!("{}: {}", type_prefix, smt_val),
            raw: JsonValue::String(smt_val.to_string()),
        }
    }
}

/// Render an unsigned integer from an SMT value string.
fn render_uint(smt_val: &str, uint_ty: UintTy) -> CexValue {
    let type_prefix = match uint_ty {
        UintTy::U8 => "u8",
        UintTy::U16 => "u16",
        UintTy::U32 => "u32",
        UintTy::U64 => "u64",
        UintTy::U128 => "u128",
        UintTy::Usize => "usize",
    };
    let width = uint_ty.bit_width();

    if let Some(bits) = parse_bitvec(smt_val) {
        // Mask to the appropriate width
        let mask = if width >= 128 {
            u128::MAX
        } else {
            (1u128 << width).wrapping_sub(1)
        };
        let val = bits & mask;
        // For u64 and smaller, use u64 JSON number; for u128 use string if needed
        if val <= u64::MAX as u128 {
            CexValue {
                display: format!("{}: {}", type_prefix, val),
                raw: JsonValue::Number(serde_json::Number::from(val as u64)),
            }
        } else {
            CexValue {
                display: format!("{}: {}", type_prefix, val),
                raw: JsonValue::String(val.to_string()),
            }
        }
    } else if let Ok(n) = smt_val.parse::<u64>() {
        CexValue {
            display: format!("{}: {}", type_prefix, n),
            raw: JsonValue::Number(serde_json::Number::from(n)),
        }
    } else {
        CexValue {
            display: format!("{}: {}", type_prefix, smt_val),
            raw: JsonValue::String(smt_val.to_string()),
        }
    }
}

/// Render a boolean SMT value.
fn render_bool(smt_val: &str) -> CexValue {
    let b = smt_val == "true";
    CexValue {
        display: format!("bool: {}", b),
        raw: JsonValue::Bool(b),
    }
}

/// Render a struct value from an SMT string.
///
/// For Phase 19 the SMT struct encoding uses field selectors in the model.
/// When no field data is embedded in `smt_val`, we emit the name with no fields.
/// Full recursive rendering is supported when field values are available.
fn render_struct(smt_val: &str, name: &str, fields: &[(String, Ty)]) -> CexValue {
    // Z3 struct model values for simple structs may come as constructor applications:
    // e.g., "(mk-Point #x00000003 #xffffffff)"
    // We attempt to parse out the field values from the constructor application.
    if let Some(inner) = smt_val.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        let tokens: Vec<&str> = inner.splitn(fields.len() + 2, ' ').collect();
        // tokens[0] is the constructor name, tokens[1..] are field values
        if tokens.len() > fields.len() {
            let field_vals: Vec<String> = fields
                .iter()
                .enumerate()
                .map(|(i, (fname, fty))| {
                    let fval = tokens.get(i + 1).copied().unwrap_or("?");
                    let cv = render_typed_value(fval, fty);
                    format!("{}: {}", fname, cv.display)
                })
                .collect();
            let display = format!("{} {{ {} }}", name, field_vals.join(", "));
            let raw_obj: serde_json::Map<String, JsonValue> = fields
                .iter()
                .enumerate()
                .map(|(i, (fname, fty))| {
                    let fval = tokens.get(i + 1).copied().unwrap_or("?");
                    let cv = render_typed_value(fval, fty);
                    (fname.clone(), cv.raw)
                })
                .collect();
            return CexValue {
                display,
                raw: JsonValue::Object(raw_obj),
            };
        }
    }

    // Fallback: emit struct name with raw value
    CexValue {
        display: format!("{} {{ {} }}", name, smt_val),
        raw: JsonValue::String(smt_val.to_string()),
    }
}

/// Render an enum value from an SMT constructor application string.
///
/// Z3 emits enum values as constructor applications like:
/// - `(mk-SomeVariant value)` → `Some(42)`
/// - `(mk-NoneVariant)` → `None`
fn render_enum(smt_val: &str, _name: &str, variants: &[(String, Vec<Ty>)]) -> CexValue {
    // Try to parse constructor application: "(mk-VariantName arg1 arg2 ...)"
    if let Some(inner) = smt_val.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        // Find the constructor name (first token)
        let mut parts = inner.splitn(2, ' ');
        let ctor_name = parts.next().unwrap_or("");
        let args_str = parts.next().unwrap_or("");

        // Strip "mk-" prefix from constructor name to get variant name
        let variant_name = ctor_name
            .strip_prefix("mk-")
            .unwrap_or(ctor_name)
            // Also handle Z3's mangling like "mk-Point_0" -> look for best match
            .to_string();

        // Find matching variant
        if let Some((vname, vtys)) = variants
            .iter()
            .find(|(vn, _)| variant_name.starts_with(vn.as_str()) || variant_name == vn.as_str())
        {
            if vtys.is_empty() {
                // Unit variant
                return CexValue {
                    display: vname.clone(),
                    raw: JsonValue::String(vname.clone()),
                };
            }
            // Variant with payload(s)
            let arg_displays: Vec<String> = vtys
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    // Extract i-th argument from args_str (space-separated)
                    let arg = if i == 0 && vtys.len() == 1 {
                        args_str
                    } else {
                        args_str.split(' ').nth(i).unwrap_or("?")
                    };
                    render_typed_value(arg, ty).display
                })
                .collect();
            let display = if arg_displays.len() == 1 {
                format!("{}({})", vname, arg_displays[0])
            } else {
                format!("{}({})", vname, arg_displays.join(", "))
            };
            let raw_args: Vec<JsonValue> = vtys
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    let arg = if i == 0 && vtys.len() == 1 {
                        args_str
                    } else {
                        args_str.split(' ').nth(i).unwrap_or("?")
                    };
                    render_typed_value(arg, ty).raw
                })
                .collect();
            let raw = if raw_args.len() == 1 {
                serde_json::json!({ vname: raw_args[0].clone() })
            } else {
                serde_json::json!({ vname: raw_args })
            };
            return CexValue { display, raw };
        }
    }

    // Fallback: check if it's just a bare variant name
    if let Some((vname, vtys)) = variants.iter().find(|(vn, _)| smt_val == vn.as_str())
        && vtys.is_empty()
    {
        return CexValue {
            display: vname.clone(),
            raw: JsonValue::String(vname.clone()),
        };
    }

    // Unknown format: return raw
    CexValue {
        display: smt_val.to_string(),
        raw: JsonValue::String(smt_val.to_string()),
    }
}

/// Render a raw pointer or reference value.
///
/// Format: `"ptr@0xADDR -> TYPE: VALUE"` where ADDR is extracted from model bits.
fn render_ptr(smt_val: &str, inner: &Ty) -> CexValue {
    // Z3 pointer addresses are typically bitvectors like #x00000001
    if let Some(addr_bits) = parse_bitvec(smt_val) {
        let addr_display = format!("ptr@0x{:x}", addr_bits);
        // For the pointee value, we don't have it directly from the model string
        // (the pointee is a separate model entry). We display the address only.
        let inner_ty_name = ty_name_string(inner);
        CexValue {
            display: format!("{} -> {}:?", addr_display, inner_ty_name),
            raw: serde_json::json!({ "ptr": format!("0x{:x}", addr_bits) }),
        }
    } else {
        CexValue {
            display: format!("ptr@{}", smt_val),
            raw: serde_json::json!({ "ptr": smt_val }),
        }
    }
}

/// Render an array or slice value.
///
/// Z3 arrays use the `((as const ...) default)` or `(store ...)` syntax.
/// For simplicity in Phase 19, we parse basic store chains up to 10 elements.
/// If more than 10 elements exist, we append "... (N more)".
const MAX_ARRAY_DISPLAY: usize = 10;

fn render_array(smt_val: &str, elem_ty: &Ty) -> CexValue {
    // Try to extract elements from Z3 store chains
    let elements = extract_array_elements(smt_val, elem_ty);
    let total = elements.len();
    let shown: Vec<&CexValue> = elements.iter().take(MAX_ARRAY_DISPLAY).collect();
    let displays: Vec<String> = shown.iter().map(|cv| cv.display.clone()).collect();
    let raws: Vec<JsonValue> = shown.iter().map(|cv| cv.raw.clone()).collect();

    let mut display = format!("[{}]", displays.join(", "));
    if total > MAX_ARRAY_DISPLAY {
        let more = total - MAX_ARRAY_DISPLAY;
        display = format!("[{}, ... ({} more)]", displays.join(", "), more);
    }

    CexValue {
        display,
        raw: JsonValue::Array(raws),
    }
}

/// Extract elements from a Z3 array model value (store chain or const).
fn extract_array_elements(smt_val: &str, elem_ty: &Ty) -> Vec<CexValue> {
    // Z3 array model: "(store (store ... default) idx val)"
    // For Phase 19 we do a best-effort parse of simple cases.
    // If the format is unrecognized, return empty or a single element.
    let mut elements: Vec<CexValue> = Vec::new();
    parse_store_chain(smt_val, elem_ty, &mut elements);
    elements
}

/// Recursively parse Z3 store chain: `(store base idx val)`.
fn parse_store_chain(smt_val: &str, elem_ty: &Ty, out: &mut Vec<CexValue>) {
    if let Some(inner) = smt_val.strip_prefix('(').and_then(|s| s.strip_suffix(')'))
        && inner.starts_with("store ")
    {
        // Parse: (store base idx val) — we only care about val
        // Simplified: find the last space-delimited token as val
        if let Some(val) = inner.split_whitespace().last() {
            let cv = render_typed_value(val, elem_ty);
            // Recursively parse the base for earlier elements
            let base_start = "store ".len();
            if let Some(base_end) = find_sexp_end(inner, base_start) {
                let base = &inner[base_start..base_end];
                parse_store_chain(base, elem_ty, out);
            }
            out.push(cv);
        }
        // If it starts with "as const" or other, ignore (default value, not a real element)
    }
}

/// Find the end index of an S-expression starting at `start` in `s`.
fn find_sexp_end(s: &str, start: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    if start >= bytes.len() {
        return None;
    }
    if bytes[start] == b'(' {
        let mut depth = 0usize;
        for (i, &b) in bytes[start..].iter().enumerate() {
            match b {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(start + i + 1);
                    }
                }
                _ => {}
            }
        }
        None
    } else {
        // Atom: ends at next space or end of string
        bytes[start..]
            .iter()
            .position(|&b| b == b' ')
            .map(|p| start + p)
            .or(Some(bytes.len()))
    }
}

/// Render a tuple value.
fn render_tuple(smt_val: &str, fields: &[Ty]) -> CexValue {
    if fields.is_empty() {
        return CexValue {
            display: "()".to_string(),
            raw: JsonValue::Array(vec![]),
        };
    }
    // Try constructor application like struct
    if let Some(inner) = smt_val.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        let tokens: Vec<&str> = inner.splitn(fields.len() + 2, ' ').collect();
        if tokens.len() > fields.len() {
            let displays: Vec<String> = fields
                .iter()
                .enumerate()
                .map(|(i, fty)| {
                    let fval = tokens.get(i + 1).copied().unwrap_or("?");
                    render_typed_value(fval, fty).display
                })
                .collect();
            let raws: Vec<JsonValue> = fields
                .iter()
                .enumerate()
                .map(|(i, fty)| {
                    let fval = tokens.get(i + 1).copied().unwrap_or("?");
                    render_typed_value(fval, fty).raw
                })
                .collect();
            return CexValue {
                display: format!("({})", displays.join(", ")),
                raw: JsonValue::Array(raws),
            };
        }
    }
    CexValue {
        display: smt_val.to_string(),
        raw: JsonValue::String(smt_val.to_string()),
    }
}

// ============================================================================
// Internal Utilities
// ============================================================================

/// Get the Rust type name string for a given type.
pub fn ty_name_string(ty: &Ty) -> String {
    match ty {
        Ty::Int(IntTy::I8) => "i8".to_string(),
        Ty::Int(IntTy::I16) => "i16".to_string(),
        Ty::Int(IntTy::I32) => "i32".to_string(),
        Ty::Int(IntTy::I64) => "i64".to_string(),
        Ty::Int(IntTy::I128) => "i128".to_string(),
        Ty::Int(IntTy::Isize) => "isize".to_string(),
        Ty::Uint(UintTy::U8) => "u8".to_string(),
        Ty::Uint(UintTy::U16) => "u16".to_string(),
        Ty::Uint(UintTy::U32) => "u32".to_string(),
        Ty::Uint(UintTy::U64) => "u64".to_string(),
        Ty::Uint(UintTy::U128) => "u128".to_string(),
        Ty::Uint(UintTy::Usize) => "usize".to_string(),
        Ty::Bool => "bool".to_string(),
        Ty::Struct(name, _) => name.clone(),
        Ty::Enum(name, _) => name.clone(),
        Ty::RawPtr(inner, Mutability::Mutable) => format!("*mut {}", ty_name_string(inner)),
        Ty::RawPtr(inner, Mutability::Shared) => format!("*const {}", ty_name_string(inner)),
        Ty::Ref(inner, Mutability::Mutable) => format!("&mut {}", ty_name_string(inner)),
        Ty::Ref(inner, Mutability::Shared) => format!("&{}", ty_name_string(inner)),
        Ty::Array(elem, n) => format!("[{}; {}]", ty_name_string(elem), n),
        Ty::Slice(elem) => format!("[{}]", ty_name_string(elem)),
        Ty::Tuple(fields) => {
            let parts: Vec<String> = fields.iter().map(ty_name_string).collect();
            format!("({})", parts.join(", "))
        }
        Ty::Unit => "()".to_string(),
        Ty::Float(ir::FloatTy::F32) => "f32".to_string(),
        Ty::Float(ir::FloatTy::F64) => "f64".to_string(),
        Ty::Char => "char".to_string(),
        Ty::Never => "!".to_string(),
        Ty::SpecInt => "SpecInt".to_string(),
        Ty::SpecNat => "SpecNat".to_string(),
        Ty::Named(n) => n.clone(),
        Ty::Generic(n) => n.clone(),
        Ty::Closure(_) => "Closure".to_string(),
        Ty::TraitObject(n) => format!("dyn {}", n),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_analysis::ir::{IntTy, Local, Ty, UintTy};
    use std::collections::HashMap;

    // ---- parse_bitvec tests ----

    #[test]
    fn parse_bitvec_hex_basic() {
        assert_eq!(parse_bitvec("#x00000005"), Some(5u128));
        assert_eq!(parse_bitvec("#x0000002a"), Some(42u128));
        assert_eq!(parse_bitvec("#x00000000"), Some(0u128));
    }

    #[test]
    fn parse_bitvec_hex_negative_pattern() {
        // #xffffffff = 4294967295 as u128 (bit pattern for -1 in i32)
        assert_eq!(parse_bitvec("#xffffffff"), Some(0xffff_ffffu128));
    }

    #[test]
    fn parse_bitvec_binary() {
        assert_eq!(parse_bitvec("#b00000101"), Some(5u128));
        assert_eq!(parse_bitvec("#b0"), Some(0u128));
        assert_eq!(parse_bitvec("#b1"), Some(1u128));
    }

    #[test]
    fn parse_bitvec_not_bitvec() {
        assert_eq!(parse_bitvec("42"), None);
        assert_eq!(parse_bitvec("true"), None);
        assert_eq!(parse_bitvec(""), None);
        assert_eq!(parse_bitvec("#x"), None);
        assert_eq!(parse_bitvec("#b"), None);
    }

    // ---- bitvec_to_signed tests ----

    #[test]
    fn bitvec_to_signed_positive_i32() {
        // #x00000005 = 5
        assert_eq!(bitvec_to_signed(5, 32), 5i128);
    }

    #[test]
    fn bitvec_to_signed_negative_i32() {
        // #xffffffff = -1 as i32
        assert_eq!(bitvec_to_signed(0xffff_ffff, 32), -1i128);
    }

    #[test]
    fn bitvec_to_signed_min_i32() {
        // #x80000000 = i32::MIN = -2147483648
        assert_eq!(bitvec_to_signed(0x8000_0000, 32), i128::from(i32::MIN));
    }

    #[test]
    fn bitvec_to_signed_max_i32() {
        // #x7fffffff = i32::MAX = 2147483647
        assert_eq!(bitvec_to_signed(0x7fff_ffff, 32), i128::from(i32::MAX));
    }

    // ---- render_int tests ----

    #[test]
    fn render_int_hex_positive() {
        // #x00000005 with i32 -> "i32: 5"
        let cv = render_int("#x00000005", IntTy::I32);
        assert_eq!(cv.display, "i32: 5");
        assert_eq!(cv.raw, serde_json::json!(5));
    }

    #[test]
    fn render_int_hex_negative() {
        // #xffffffff with i32 -> "i32: -1"
        let cv = render_int("#xffffffff", IntTy::I32);
        assert_eq!(cv.display, "i32: -1");
        assert_eq!(cv.raw, serde_json::json!(-1));
    }

    #[test]
    fn render_int_decimal_fallback() {
        // Plain decimal "42" with i32 -> "i32: 42"
        let cv = render_int("42", IntTy::I32);
        assert_eq!(cv.display, "i32: 42");
    }

    #[test]
    fn render_int_i8() {
        let cv = render_int("#xff", IntTy::I8);
        assert_eq!(cv.display, "i8: -1");
    }

    #[test]
    fn render_int_isize() {
        let cv = render_int("#x0000000000000001", IntTy::Isize);
        assert_eq!(cv.display, "isize: 1");
    }

    // ---- render_uint tests ----

    #[test]
    fn render_uint_hex_basic() {
        // #x0000002a with u32 -> "u32: 42"
        let cv = render_uint("#x0000002a", UintTy::U32);
        assert_eq!(cv.display, "u32: 42");
        assert_eq!(cv.raw, serde_json::json!(42u64));
    }

    #[test]
    fn render_uint_all_ones_u32() {
        // #xffffffff with u32 -> "u32: 4294967295"
        let cv = render_uint("#xffffffff", UintTy::U32);
        assert_eq!(cv.display, "u32: 4294967295");
    }

    #[test]
    fn render_uint_u8() {
        let cv = render_uint("#xff", UintTy::U8);
        assert_eq!(cv.display, "u8: 255");
    }

    // ---- render_bool tests ----

    #[test]
    fn render_bool_true() {
        let cv = render_bool("true");
        assert_eq!(cv.display, "bool: true");
        assert_eq!(cv.raw, serde_json::json!(true));
    }

    #[test]
    fn render_bool_false() {
        let cv = render_bool("false");
        assert_eq!(cv.display, "bool: false");
        assert_eq!(cv.raw, serde_json::json!(false));
    }

    #[test]
    fn render_bool_unknown_value_treated_as_false() {
        // Any non-"true" value is treated as false (Z3 only emits "true"/"false")
        let cv = render_bool("other");
        assert_eq!(cv.display, "bool: false");
    }

    // ---- render_typed_value dispatch tests ----

    #[test]
    fn render_typed_value_int() {
        let cv = render_typed_value("#x00000005", &Ty::Int(IntTy::I32));
        assert_eq!(cv.display, "i32: 5");
    }

    #[test]
    fn render_typed_value_uint() {
        let cv = render_typed_value("#x0000002a", &Ty::Uint(UintTy::U32));
        assert_eq!(cv.display, "u32: 42");
    }

    #[test]
    fn render_typed_value_bool() {
        let cv = render_typed_value("false", &Ty::Bool);
        assert_eq!(cv.display, "bool: false");
    }

    #[test]
    fn render_typed_value_named_fallback() {
        // Named/unknown types fall back to raw string
        let cv = render_typed_value("some_smt_value", &Ty::Named("SomeType".to_string()));
        assert_eq!(cv.display, "some_smt_value");
    }

    // ---- render_counterexample: ghost filtering ----

    #[test]
    fn render_counterexample_excludes_ghost_locals() {
        let model = vec![
            ("_1".to_string(), "#x00000005".to_string()),
            ("_2".to_string(), "true".to_string()),
        ];
        let mut source_names = HashMap::new();
        source_names.insert("_1".to_string(), "x".to_string());
        source_names.insert("_2".to_string(), "__ghost_spec_x".to_string());

        let locals = vec![
            Local::new("_1", Ty::Int(IntTy::I32)),
            Local::ghost("_2", Ty::Bool), // ghost — must be excluded
        ];
        let params: Vec<Local> = vec![];

        let result = render_counterexample(&model, &source_names, &locals, &params);

        // Only "_1" (x) should appear; "_2" (ghost) must be excluded
        assert_eq!(result.len(), 1, "ghost variable must be excluded");
        assert_eq!(result[0].name, "x");
        assert_eq!(result[0].display, "i32: 5");
    }

    // ---- render_counterexample: source name substitution ----

    #[test]
    fn render_counterexample_substitutes_source_names() {
        let model = vec![("_1".to_string(), "#x00000005".to_string())];
        let mut source_names = HashMap::new();
        source_names.insert("_1".to_string(), "x".to_string());

        let locals = vec![Local::new("_1", Ty::Int(IntTy::I32))];
        let params: Vec<Local> = vec![];

        let result = render_counterexample(&model, &source_names, &locals, &params);

        assert_eq!(result.len(), 1);
        assert_eq!(
            result[0].name, "x",
            "SSA name must be replaced with source name"
        );
        assert_eq!(result[0].ty, "i32");
        assert_eq!(result[0].display, "i32: 5");
        assert_eq!(result[0].raw, serde_json::json!(5));
    }

    // ---- render_counterexample: SSA name fallback when no source name ----

    #[test]
    fn render_counterexample_keeps_ssa_name_when_no_source_name() {
        let model = vec![("_3".to_string(), "false".to_string())];
        let source_names = HashMap::new();

        let locals = vec![Local::new("_3", Ty::Bool)];
        let params: Vec<Local> = vec![];

        let result = render_counterexample(&model, &source_names, &locals, &params);

        assert_eq!(result.len(), 1);
        assert_eq!(
            result[0].name, "_3",
            "SSA name kept when no source name mapping"
        );
        assert_eq!(result[0].display, "bool: false");
    }

    // ---- render_counterexample: bool SMT value ----

    #[test]
    fn render_counterexample_bool_false() {
        let model = vec![("_2".to_string(), "false".to_string())];
        let mut source_names = HashMap::new();
        source_names.insert("_2".to_string(), "flag".to_string());

        let locals = vec![Local::new("_2", Ty::Bool)];
        let params: Vec<Local> = vec![];

        let result = render_counterexample(&model, &source_names, &locals, &params);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0].display, "bool: false");
        assert_eq!(result[0].raw, serde_json::json!(false));
    }

    // ---- render_counterexample: u32 bitvec ----

    #[test]
    fn render_counterexample_u32_bitvec() {
        let model = vec![("_3".to_string(), "#x0000002a".to_string())];
        let mut source_names = HashMap::new();
        source_names.insert("_3".to_string(), "count".to_string());

        let locals = vec![Local::new("_3", Ty::Uint(UintTy::U32))];
        let params: Vec<Local> = vec![];

        let result = render_counterexample(&model, &source_names, &locals, &params);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0].display, "u32: 42");
    }

    // ---- render_counterexample: params are included ----

    #[test]
    fn render_counterexample_includes_params() {
        let model = vec![("_1".to_string(), "#x00000003".to_string())];
        let mut source_names = HashMap::new();
        source_names.insert("_1".to_string(), "n".to_string());

        let locals: Vec<Local> = vec![];
        let params = vec![Local::new("_1", Ty::Int(IntTy::I32))];

        let result = render_counterexample(&model, &source_names, &locals, &params);

        assert_eq!(result.len(), 1);
        assert_eq!(result[0].name, "n");
        assert_eq!(result[0].display, "i32: 3");
    }

    // ---- ty_name_string tests ----

    #[test]
    fn ty_name_string_primitives() {
        assert_eq!(ty_name_string(&Ty::Int(IntTy::I32)), "i32");
        assert_eq!(ty_name_string(&Ty::Uint(UintTy::U64)), "u64");
        assert_eq!(ty_name_string(&Ty::Bool), "bool");
        assert_eq!(ty_name_string(&Ty::Unit), "()");
    }
}
