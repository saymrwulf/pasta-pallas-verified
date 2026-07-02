-- Hand-written models for external functions (derived from FunsExternal_Template.lean).
-- [pasta_curves]: external functions.
--
-- Modeling policy (same as the ed25519 repos):
--  * `subtle` items whose Rust bodies are real bit math are modeled FAITHFULLY
--    (ct_eq decides equality; select/bitand/not collapse to if-then-else /
--    boolean algebra on the documented {0,1} Choice invariant).
--  * `subtle` items whose Rust bodies are optimization barriers (black_box)
--    are semantically the identity and modeled so (Choice::from, unwrap_u8).
--  * core `as_ref`/`borrow` on arrays/references are the evident coercions.
--  * Everything else stays an AXIOM: Debug fmt, Ord/cmp, Sum/Product folds,
--    sqrt/sqrt_ratio/random and the sqrt-table helpers, ff trait defaults —
--    all deliberately opaque, all outside every certificate cone
--    (verified by the check.sh Phase-3 axiom audit).
import Aeneas
import PallasFp.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open pasta_curves

/-- [core::array::{impl core::convert::AsRef<[T]> for [T; N]}::as_ref]
    MODEL: an array viewed as a slice — `Array.to_slice`. Needed transparently
    by `pow_vartime` (`exp.as_ref()`). -/
@[rust_fun "core::array::{core::convert::AsRef<[@T; @N], [@T]>}::as_ref"]
def Array.Insts.CoreConvertAsRefSlice.as_ref
  {T : Type} {N : Std.Usize} : Array T N → Result (Slice T) :=
  fun a => ok a.to_slice

/-- [core::array::{impl core::convert::AsMut<[T]> for [T; N]}::as_mut]
    AXIOM: not reachable from any transparent function in this extraction. -/
@[rust_fun "core::array::{core::convert::AsMut<[@T; @N], [@T]>}::as_mut"]
axiom Array.Insts.CoreConvertAsMutSlice.as_mut
  {T : Type} {N : Std.Usize} :
  Array T N → Result ((Slice T) × (Slice T → Array T N))

/-- [core::borrow::{impl core::borrow::Borrow<T> for T}::borrow]
    MODEL: identity (Rust's blanket Borrow is `&self` — value semantics id). -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T := fun x => ok x

/-- [core::borrow::{impl core::borrow::Borrow<T> for &'_0 T}::borrow]
    MODEL: identity. -/
@[rust_fun "core::borrow::{core::borrow::Borrow<&'0 @T, @T>}::borrow"]
def Shared0T.Insts.CoreBorrowBorrow.borrow {T : Type} : T → Result T := fun x => ok x

/-- [core::convert::{impl core::convert::AsRef<U> for &'_0 T}::as_ref]
    MODEL: defer to the underlying instance (deref transparent). -/
@[rust_fun "core::convert::{core::convert::AsRef<&'0 @T, @U>}::as_ref"]
def Shared0T.Insts.CoreConvertAsRef.as_ref
  {T : Type} {U : Type} (AsRefInst : core.convert.AsRef T U) : T → Result U :=
  fun x => AsRefInst.as_ref x

/-- [ff::Field::sqrt] (trait DEFAULT method)
    AXIOM: dead — `Fp` overrides `sqrt`; the default body is never called. -/
@[rust_fun "ff::Field::sqrt"]
axiom ff.Field.sqrt.default
  {Self : Type} (FieldInst : ff.Field Self) :
  Self → Result (subtle.CtOption Self)

/-- [ff::Field::pow_vartime] (trait DEFAULT method)
    AXIOM: dead — `Fp` overrides `pow_vartime` (the patched index-loop version,
    translated transparently in Funs.lean); the default body is never called. -/
@[rust_fun "ff::Field::pow_vartime"]
axiom ff.Field.pow_vartime.default
  {Self : Type} {S : Type} (FieldInst : ff.Field Self)
  (coreconvertAsRefSSliceU64Inst : core.convert.AsRef S (Slice Std.U64)) :
  Self → S → Result Self

/-- [ff::PrimeField::from_u128] (trait DEFAULT method) — AXIOM: dead code here. -/
@[rust_fun "ff::PrimeField::from_u128"]
axiom ff.PrimeField.from_u128.default
  {Self : Type} {Clause0_Repr : Type} (PrimeFieldInst : ff.PrimeField Self
  Clause0_Repr) :
  Std.U128 → Result Self

/-- [subtle::{subtle::Choice}::unwrap_u8]
    MODEL: identity — Rust body is `self.0` behind a black_box fence. -/
@[rust_fun "subtle::{subtle::Choice}::unwrap_u8"]
def subtle.Choice.unwrap_u8 : subtle.Choice → Result Std.U8 := fun c => ok c

/-- [subtle::{impl BitAnd for Choice}::bitand]
    MODEL: u8 bitwise AND (on the {0,1} invariant this is boolean ∧). -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
def subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand
  : subtle.Choice → subtle.Choice → Result subtle.Choice :=
  fun a b => ok (a &&& b)

/-- [subtle::{impl Not for Choice}::not]
    MODEL: `1 ^ c` — Rust body is `Choice(1u8 ^ self.0)`; on {0,1} this is ¬. -/
@[rust_fun
  "subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not"]
def subtle.Choice.Insts.CoreOpsBitNotChoice.not
  : subtle.Choice → Result subtle.Choice :=
  fun c => ok (1#u8 ^^^ c)

/-- [subtle::{impl From<u8> for Choice}::from]
    MODEL: identity — Rust body reads the byte through a volatile/black_box
    optimization fence; value semantics is id. (Callers uphold the {0,1}
    contract; the crate's ct_eq-style producers only ever pass 0 or 1.) -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
def subtle.Choice.Insts.CoreConvertFromU8.from
  : Std.U8 → Result subtle.Choice := fun x => ok x

/-- [subtle::{impl ConstantTimeEq for u64}::ct_eq]
    MODEL: the SPECIFICATION of subtle's xor/wrapping-neg/shift bit trick,
    which returns 1 iff the two integers are equal (for ALL inputs): decide
    `a = b`. -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u64>}::ct_eq"]
def U64.Insts.SubtleConstantTimeEq.ct_eq
  : Std.U64 → Std.U64 → Result subtle.Choice :=
  fun a b => ok (if a.val = b.val then 1#u8 else 0#u8)

/-- [subtle::{impl ConditionallySelectable for u64}::conditional_select]
    MODEL: `a ^ (mask & (a ^ b))` with mask = −(c as u64): equals `a` when
    c = 0 and `b` when c = 1. Every Choice reaching this call is 0 or 1
    (see TypesExternal policy), so if-then-else is exact. -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
def U64.Insts.SubtleConditionallySelectable.conditional_select
  : Std.U64 → Std.U64 → subtle.Choice → Result Std.U64 :=
  fun a b c => ok (if c.val = 0 then a else b)

/-- [subtle::{subtle::CtOption<T>}::new]
    MODEL: the struct constructor — store (value, is_some) verbatim. -/
@[rust_fun "subtle::{subtle::CtOption<@T>}::new"]
def subtle.CtOption.new
  {T : Type} : T → subtle.Choice → Result (subtle.CtOption T) :=
  fun v c => ok ⟨v, c⟩

/-- [Fp Debug::fmt] — AXIOM: formatting, no proof depends on it. -/
axiom fields.fp.Fp.Insts.CoreFmtDebug.fmt
  :
  fields.fp.Fp → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [Fp PartialOrd::partial_cmp] — AXIOM: deliberately opaque (iterator fold). -/
axiom fields.fp.Fp.Insts.CoreCmpPartialOrdFp.partial_cmp
  : fields.fp.Fp → fields.fp.Fp → Result (Option Ordering)

/-- [Fp Ord::cmp] — AXIOM: deliberately opaque (iterator fold). -/
axiom fields.fp.Fp.Insts.CoreCmpOrd.cmp
  : fields.fp.Fp → fields.fp.Fp → Result Ordering

/-- [Fp Sum::sum] — AXIOM: deliberately opaque (iterator fold). -/
axiom fields.fp.Fp.Insts.CoreIterTraitsAccumSum.sum
  {T : Type} {I : Type} (coreborrowBorrowTFpInst : core.borrow.Borrow T
  fields.fp.Fp) (coreitertraitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I T) :
  I → Result fields.fp.Fp

/-- [Fp Product::product] — AXIOM: deliberately opaque (iterator fold). -/
axiom fields.fp.Fp.Insts.CoreIterTraitsAccumProduct.product
  {T : Type} {I : Type} (coreborrowBorrowTFpInst : core.borrow.Borrow T
  fields.fp.Fp) (coreitertraitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I T) :
  I → Result fields.fp.Fp

/-- [Fp ff::Field::sqrt] — AXIOM: Tonelli–Shanks via helpers; out of scope
    for the field certificate (documented in TRUSTED-BASE.md). -/
axiom fields.fp.Fp.Insts.FfField.sqrt
  : fields.fp.Fp → Result (subtle.CtOption fields.fp.Fp)

/-- [Fp ff::Field::sqrt_ratio] — AXIOM: out of scope (see sqrt). -/
axiom fields.fp.Fp.Insts.FfField.sqrt_ratio
  : fields.fp.Fp → fields.fp.Fp → Result (subtle.Choice × fields.fp.Fp)

/-- [Fp ff::Field::random] — AXIOM: RNG plumbing, untranslatable and irrelevant. -/
axiom fields.fp.Fp.Insts.FfField.random
  {T0 : Type} (rand_coreRngCoreInst : rand_core.RngCore T0) :
  T0 → Result fields.fp.Fp

/-- [Fp SqrtTableHelpers::get_lower_32] — AXIOM: sqrt-table helper, opaque. -/
axiom
  fields.fp.Fp.Insts.Pasta_curvesArithmeticFieldsSqrtTableHelpersArrayU832.get_lower_32
  : fields.fp.Fp → Result Std.U32

/-- [Fp SqrtTableHelpers::pow_by_t_minus1_over2] — AXIOM: sqrt-table helper
    (closure-based), opaque. -/
axiom
  fields.fp.Fp.Insts.Pasta_curvesArithmeticFieldsSqrtTableHelpersArrayU832.pow_by_t_minus1_over2
  : fields.fp.Fp → Result fields.fp.Fp

/-- [Fp WithSmallOrderMulGroup::ZETA] — AXIOM: constant of an opaque impl. -/
axiom fields.fp.Fp.Insts.FfWithSmallOrderMulGroupArrayU8323.ZETA
  : Result fields.fp.Fp

/-- [Fp FromUniformBytes::from_uniform_bytes] — AXIOM: opaque impl. -/
axiom fields.fp.Fp.Insts.FfFromUniformBytesArrayU83264.from_uniform_bytes
  : Array Std.U8 64#usize → Result fields.fp.Fp
