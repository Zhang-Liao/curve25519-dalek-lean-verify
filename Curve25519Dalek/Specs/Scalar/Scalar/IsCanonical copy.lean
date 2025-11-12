/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
-- import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Scalar.Scalar.Reduce
import Curve25519Dalek.Specs.Scalar.Scalar.CtEq

/-! # Spec Theorem for `Scalar::is_canonical`

Specification and proof for `Scalar::is_canonical`.

This function checks if the representation is canonical.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Returns True if the input Scalar s is the canonical
      representative modulo \ell within the scalar field, i.e.,
      if s \in \{0,…, \ell – 1\}, else returns False.

natural language specs:

    • scalar_to_nat(s) \in \{0,…, \ell - 1 \} \iff Return value = True
-/


lemma sum_split_at {N j : ℕ} (hj : j < N) (f : ℕ → Nat) : ∑ i ∈ Finset.range N, f i
    = (∑ i ∈ Finset.range j, f i)
      + f j
      + (∑ i ∈ Finset.Ico (j+1) N, f i) := by
  rw [← Finset.sum_range_add_sum_Ico f (Nat.succ_le_of_lt hj)]
  simp
  rw [Finset.sum_range_succ]

lemma U8_as_Nat_injective : Function.Injective (fun (x : U8) => (x : Nat)) := by
  unfold Function.Injective
  intro a1 a2 h
  simp at h
  apply UScalar.eq_of_val_eq
  exact h

lemma array_ext : ∀ (a1 a2 : Aeneas.Std.Array U8 32#usize), (∀ i : Fin 32, a1[i]! = a2[i]!) -> a1 = a2 := by
  intro a1 a2 h
  apply Subtype.eq
  ext i hi
  by_cases hbound : i < 32
  · have hval1 : (↑a1)[i]? = some (a1[i]!) := by simp [hbound]
    have hval2 : (↑a2)[i]? = some (a2[i]!) := by simp [hbound]
    let fin_i : Fin 32 := ⟨i, hbound⟩
    have h_arr_eq : a1[fin_i]! = a2[fin_i]! := h fin_i
    simp at h_arr_eq
    have h1 : a1[fin_i]! = a1[i]! := by simp [fin_i]
    have h2 : a2[fin_i]! = a2[i]! := by simp [fin_i]
    constructor <;> grind
  · have hn1 : (↑a1)[i]? = none
    := by simp [hbound]
    have hn2 : (↑a2)[i]? = none := by simp [hbound]
    grind

-- lemma U8x32_as_Nat_coeff_extract1 (a1 : Array U8 32#usize) :=

--   sorry
-- lemma sum_test (a1 : Array U8 32#usize) : (∑ i ∈ Finset.range 32, 2 ^ (8 * i) * a1.val[i]!) = 2 ^ 256 - 1 := by
--   sorry
set_option diagnostics true

lemma U8x32_as_Nat_injective : Function.Injective U8x32_as_Nat := by
  unfold Function.Injective
  intro a1 a2
  have coeff_extract1 : ∀ (i : Fin 32),
    ((U8x32_as_Nat a1) / (256 ^ i.val)) % 256 = (a1[i]!).val := by
    intro j
    have hj : j.val < 32 := j.is_lt
    unfold U8x32_as_Nat
    unfold Finset.sum
    have rw_pow: (fun i => 2 ^ (8 * i) * a1[i]!.val) = (fun i => 256 ^ i * a1[i]!.val) := by
      ext i
      simp [pow_mul]
    rw [rw_pow]
    have sum_eq : (Multiset.map (fun i ↦ 256 ^ i * a1[i]!.val) (Finset.range 32).val).sum =
    (∑ i ∈ Finset.range 32, 256 ^ i * a1[i]!.val) := by rw [Finset.sum_eq_multiset_sum]
    rw [sum_eq]
    rw [sum_split_at (Nat.succ_le_of_lt hj)]
    clear sum_eq
    have div_eq : (∑ i ∈ Finset.range 32, 256 ^ i * a1[i]!.val) / 256 ^ j.val = (∑ i ∈ Finset.range j.val, 256 ^ (i- j.val) * a1[i]!.val) := by
      sorry
    sorry
  sorry
--     unfold U8x32_as_Nat
--     intro j
--     -- sorry

--     rw [sum_split_at hj]
--     have h_low : (∑ x ∈ Finset.range j.val, 2^(8*x) * (a1.val[x]! : ℕ)) < 256 ^ j.val := by
--       -- 证明 range j 的部分小于 256^j
--       sorry
--     have h_high_mult : 256^j.val ∣ (∑ i ∈ Finset.Ico (j.val+1) 32, 2^(8*i) * (a1.val[i]! : ℕ)) := by
--       sorry
--       -- simp
--     rw [h_high_mult]

--     sorry
--   have coeff_extract2 : ∀ (i : Fin 32),
--     ((U8x32_as_Nat a2) / (256 ^ i.val)) % 256 = (a2[i]!).val := by sorry
--   have arr_eqs: ∀ i : Fin 32, a1[i]! = a2[i]! := by
--     intro i
--     have h1 := coeff_extract1 i
--     have h2 := coeff_extract2 i
--     rw [h] at h1
--     rw [h2] at h1
--     symm
--     apply U8_as_Nat_injective
--     exact h1
--   apply array_ext
--   exact arr_eqs


-- /-- **Spec and proof concerning `scalar.Scalar.is_canonical`**:
-- - No panic (always returns successfully)
-- - Returns Choice.one if and only if the scalar's bytes represent a value less than L (the group order)
-- -/
@[progress]
theorem is_canonical_spec (s : Scalar) :
    ∃ c,
    is_canonical s = ok c ∧
    (c = Choice.one ↔ U8x32_as_Nat s.bytes < L)
    := by
  unfold is_canonical
  progress*
  rw [res_post]
  constructor
  · grind
  · intro h
    rename_i s' _
    have bytes_eq : U8x32_as_Nat s.bytes = U8x32_as_Nat s'.bytes := Nat.ModEq.eq_of_lt_of_lt s_post_1 s_post_2 h
    apply U8x32_as_Nat_injective
    symm
    exact bytes_eq

end curve25519_dalek.scalar.Scalar
