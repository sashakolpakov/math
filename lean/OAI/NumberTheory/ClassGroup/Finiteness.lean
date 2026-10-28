import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.FractionalIdeal.Operations

/-! # Finiteness -/

namespace OAI.NumberTheory.ClassGroup.Finiteness

open scoped _root_.NumberField nonZeroDivisors

/-
All ideals are fractional ideals of the full ring of integers. The proof uses
Mathlib's finiteness theorem and raises an ideal class to the class number.
This file does not import the statement placeholders or other graph results.
-/

theorem classGroup_finite
    (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) := by
  infer_instance

theorem fractionalIdeal_pow_principal
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ (m : ℕ) (α : K),
      0 < m ∧ α ≠ 0 ∧
      I ^ m = FractionalIdeal.spanSingleton (𝓞 K)⁰ α := by
  let m := Fintype.card (ClassGroup (𝓞 K))
  let u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI
  have hm : 0 < m := Fintype.card_pos
  have hu : ClassGroup.mk K (u ^ m) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one
  have hp : ((I ^ m : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal := by
    simpa [u] using (ClassGroup.mk_eq_one_iff.mp hu)
  obtain ⟨α, hα⟩ := (FractionalIdeal.isPrincipal_iff (I ^ m)).mp hp
  refine ⟨m, α, hm, ?_, hα⟩
  intro hzero
  apply pow_ne_zero m hI
  simpa [hzero] using hα

end OAI.NumberTheory.ClassGroup.Finiteness
