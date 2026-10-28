import OAI.RepresentationTheory.Theta.Adelic.RationalCharacterPairing
import Mathlib.RingTheory.Localization.Integer

/-! # Character Dual Lattice -/

namespace OAI.RepresentationTheory.Theta.Adelic.CharacterDualLattice

noncomputable section

/-! A uniform integral denominator for the rational dual of the integer
lattice under a nonzero rational multiplication functional. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

def multiplicationPairing (ℓ : F →ₗ[ℚ] ℚ) : LinearMap.BilinForm ℚ F :=
  (LinearMap.mul ℚ F).compr₂ ℓ

theorem multiplicationPairing_nondegenerate (ℓ : F →ₗ[ℚ] ℚ) (hℓ : ℓ ≠ 0) :
    (multiplicationPairing F ℓ).Nondegenerate := by
  have hnonzero : ∃ a : F, ℓ a ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hℓ (LinearMap.ext h)
  have hleft : ∀ x : F, (∀ y, ℓ (x * y) = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    obtain ⟨a, ha⟩ := hnonzero
    have he := hx (x⁻¹ * a)
    rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at he
    exact ha he
  refine ⟨hleft, ?_⟩
  intro y hy
  apply hleft y
  intro x
  have he := hy x
  change ℓ (x * y) = 0 at he
  simpa only [mul_comm] using he

theorem rational_dual_lattice_denominator
    (ℓ : F →ₗ[ℚ] ℚ) (hℓ : ℓ ≠ 0) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ a : F,
      (∀ b : 𝓞 F, ∃ z : ℤ, (z : ℚ) = ℓ (a * algebraMap (𝓞 F) F b)) →
      ∃ s : 𝓞 F, algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F r * a := by
  let B := multiplicationPairing F ℓ
  have hB : B.Nondegenerate := multiplicationPairing_nondegenerate F ℓ hℓ
  let b := B.dualBasis hB (integralBasis F)
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (𝓞 F)) b
  refine ⟨r.val, nonZeroDivisors.ne_zero r.property, fun a ha => ?_⟩
  choose z hz using fun i => ha (RingOfIntegers.basis F i)
  have hcoord (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
      b.repr a i = (z i : ℚ) := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    change ℓ (a * integralBasis F i) = (z i : ℚ)
    simpa only [integralBasis_apply] using (hz i).symm
  let R := (algebraMap (𝓞 F) F).range
  have hint : (r.val • a : F) ∈ R := by
    rw [← b.sum_repr a, Finset.smul_sum]
    apply R.sum_mem
    intro i _
    rw [hcoord, smul_comm, Int.cast_smul_eq_zsmul]
    exact R.zsmul_mem (hr i) (z i)
  obtain ⟨s, hs⟩ := hint
  exact ⟨s, by simpa only [Algebra.smul_def] using hs⟩

end

end OAI.RepresentationTheory.Theta.Adelic.CharacterDualLattice
