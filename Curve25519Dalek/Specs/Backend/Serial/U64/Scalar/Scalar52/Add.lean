/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Mathlib.Data.Nat.ModEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- No panic (always returns successfully)
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (u u' : Scalar52)
    (hu : ∀ i, i < 5 → (u[i]!).val < 2 ^ 52)
    (hu' : ∀ i, i < 5 → (u'[i]!).val < 2 ^ 52):
    ∃ v,
    add u u' = ok v ∧
    Scalar52_as_Nat v = (Scalar52_as_Nat u + Scalar52_as_Nat u') % L
    := by
  unfold add
  progress*
-- 首先需要 add_loop 的规范引理
  have h_add_loop : ∃ sum,
    add_loop mask u u' ZERO 0#u64 0#usize = ok sum ∧
    Scalar52_as_Nat sum = Scalar52_as_Nat u + Scalar52_as_Nat u' := by
    sorry

  obtain ⟨sum, h_sum_ok, h_sum_eq⟩ := h_add_loop
  have h_sub : ∃ v,
    sub sum constants.L = ok v
    ∧ Scalar52_as_Nat v = (Scalar52_as_Nat sum - Scalar52_as_Nat constants.L) % L := by
      have h_sum_bounds : ∀ i < 5, (sum[i]!).val < 2 ^ 52 := by
        -- 这应该从 add_loop 的规范中得出
        sorry  -- 需要 add_loop_spec 提供这个性质
      -- 证明 constants.L 的界限（应该是常数，可以用 decide）
      have h_L_bounds : ∀ i < 5, (constants.L[i]!).val < 2 ^ 52 := by
        unfold constants.L
        decide  -- 或者需要显式检查每个 limb
      -- 应用 sub_spec
      exact sub_spec sum constants.L h_sum_bounds h_L_bounds
  obtain ⟨v, h_v_ok, h_v_mod⟩ := h_sub
  use v
  constructor
  · rw [h_sum_ok]
    simp [h_v_ok]
  · rw [h_v_mod]
    rw [h_sum_eq]
    sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
