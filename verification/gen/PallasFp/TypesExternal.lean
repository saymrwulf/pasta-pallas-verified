-- Hand-written models for external types (derived from TypesExternal_Template.lean).
-- [pasta_curves]: external types.
--
-- Modeling policy (same as the ed25519 repos):
--  * `subtle.Choice` is MODELED as `Std.U8`. Rust invariant: the wrapped u8 is
--    always 0 or 1 (subtle's documented contract). Every Choice produced by
--    the models in FunsExternal.lean is literally 0 or 1, so if-then-else on
--    `c.val = 0` is exact for every value the transpiled code can construct.
--  * `subtle.CtOption T` is MODELED as a pair (value, is_some flag) — exactly
--    the Rust struct layout (`CtOption { value: T, is_some: Choice }`).
--  * `rand_core.error.Error` stays an opaque axiom: it is only reachable from
--    the (deliberately opaque) `random`, outside every certificate cone.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-- [subtle::Choice] — MODEL: a u8 carrying the {0,1} invariant. -/
@[reducible, rust_type "subtle::Choice"]
def subtle.Choice : Type := Std.U8

/-- [subtle::CtOption] — MODEL: the Rust struct `{ value: T, is_some: Choice }`. -/
@[rust_type "subtle::CtOption"]
structure subtle.CtOption (T : Type) where
  value : T
  is_some : subtle.Choice

/-- [rand_core::error::Error] — AXIOM: only reachable from the opaque `random`. -/
@[rust_type "rand_core::error::Error"]
axiom rand_core.error.Error : Type
