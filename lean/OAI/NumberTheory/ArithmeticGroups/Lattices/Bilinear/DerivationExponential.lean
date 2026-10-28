import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismTransversal
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Derivation Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DerivationExponential.Construction

noncomputable section

/-! Exponentiating a bounded derivation preserves a continuous bilinear
operation. This is proved by differentiating the transported operation. -/

open scoped Classical
open NormedSpace

theorem exp_bilinear_derivation_preserves
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    (B : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L)
    (hA : ∀ x y, A (B x y) = B (A x) y + B x (A y)) (x y : L) :
    exp A (B x y) = B (exp A x) (exp A y) := by
  let : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let F : ℝ → L := fun t => exp (t • (-A)) (B (exp (t • A) x) (exp (t • A) y))
  have hd (t : ℝ) : HasDerivAt F 0 t := by
    have hpos := hasDerivAt_exp_smul_const' A t
    have hx := hpos.clm_apply (hasDerivAt_const t x)
    have hy := hpos.clm_apply (hasDerivAt_const t y)
    have hB := (B.hasFDerivAt.comp_hasDerivAt t hx).clm_apply hy
    have hneg := hasDerivAt_exp_smul_const (-A) t
    have hF := hneg.clm_apply hB
    convert! hF using 1
    simp only [mul_apply_eq_comp, neg_apply,
      map_zero, add_zero, map_add, map_neg, Function.comp_apply]
    rw [hA, map_add]
    abel
  have hc : F 1 = F 0 := is_const_of_deriv_eq_zero
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  have he := congrArg (fun z => exp A z) hc
  have hi : exp A * exp (-A) = (1 : L →L[ℝ] L) := by
    rw [← exp_add_of_commute (Commute.refl A).neg_right, add_neg_cancel, exp_zero]
  have hi_apply (z : L) : exp A (exp (-A) z) = z := by
    exact DFunLike.congr_fun hi z
  simpa only [F, one_smul, zero_smul, exp_zero, one_apply_eq_self, hi_apply] using he.symm

theorem exp_continuousLinearMap_injective
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    (A : L →L[ℝ] L) : Function.Injective (exp A : L →L[ℝ] L) := by
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hi : exp (-A) * exp A = (1 : L →L[ℝ] L) := by
    rw [← exp_add_of_commute (Commute.refl A).neg_left, neg_add_cancel, exp_zero]
  intro x y h
  have he := congrArg (fun z => exp (-A) z) h
  have hi_apply (z : L) : exp (-A) (exp A z) = z := DFunLike.congr_fun hi z
  simpa only [hi_apply] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DerivationExponential.Construction
