import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Scaled Coefficient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ScaledCoefficient

noncomputable section

/-! Conversion between ordinary complex gradients and the Fourier-normalized Sobolev gradient preserves proved ellipticity. -/

open scoped ContDiff

variable {F D : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

def complexScaleCoefficient (c : ℂ) (A : F →L[ℝ] F) : F →L[ℝ] F :=
  let S := (c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
  S.adjoint.comp (A.comp S)

theorem complexScaleCoefficient_pair (c : ℂ) (A : F →L[ℝ] F) (v w : F) :
    inner ℝ (complexScaleCoefficient c A v) w = inner ℝ (A (c • v)) (c • w) := by
  exact ContinuousLinearMap.adjoint_inner_left
    ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ) w (A (c • v))

theorem complexScaleCoefficient_lower (c : ℂ) (A : F →L[ℝ] F) (a : ℝ)
    (hA : ∀ v : F, a * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (v : F) :
    (a * ‖c‖ ^ 2) * ‖v‖ ^ 2 ≤ inner ℝ (complexScaleCoefficient c A v) v := by
  rw [complexScaleCoefficient_pair]
  have hp := hA (c • v)
  rw [norm_smul, mul_pow, ← mul_assoc] at hp
  exact hp

theorem complexScaleCoefficient_smoothOn (c : ℂ) (A : D → F →L[ℝ] F) {U : Set D}
    (hA : ContDiffOn ℝ ∞ A U) : ContDiffOn ℝ ∞ (fun x => complexScaleCoefficient c (A x)) U :=
  contDiffOn_const.clm_comp (hA.clm_comp contDiffOn_const)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ScaledCoefficient
