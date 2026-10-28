import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient
import OAI.RepresentationTheory.Weil.Local.UnitaryInner

/-! # Gaussian Weak Continuity -/

namespace OAI.RepresentationTheory.Theta.Adelic.GaussianWeakContinuity

noncomputable section

/-! Weak continuity of positive Siegel Gaussians. Their absolute values
are at most one, so a fixed Schwartz test supplies a single integrable
bound on the entire Siegel domain. -/

open scoped Classical _root_.Matrix.Norms.Elementwise ComplexConjugate InnerProductSpace

open _root_.Matrix _root_.MeasureTheory OAI.RepresentationTheory.Weil.Local.UnitaryInner.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM

variable {N : ℕ}

theorem real_gaussian_norm_le_one (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ N) :
    ‖(AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.realSiegelGaussian Z 0).val x‖ ≤ 1 := by
  rw [AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.real_siegel_gaussian_apply, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have h := PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent_re_le Z 0 x
  simp only [norm_zero, mul_zero, zero_mul, add_zero] at h
  exact h.trans (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le Z.phase.lowerBound_pos.le)) (sq_nonneg _))

def gaussianPairing (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) : ℂ :=
  ∫ x, (AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.realSiegelGaussian Z 0).val x * conj (f.val x) ∂ Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ N

theorem gaussianPairing_inner (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    gaussianPairing Z f = ⟪Weil.Local.UnitaryInner.Construction.testToL2 ℝ N f, Weil.Local.UnitaryInner.Construction.testToL2 ℝ N (AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.realSiegelGaussian Z 0)⟫_ℂ :=
  (Weil.Local.UnitaryInner.Construction.testToL2_inner ℝ N f (AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.realSiegelGaussian Z 0)).symm

theorem gaussianPairing_self_nonzero (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) :
    gaussianPairing Z (AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.realSiegelGaussian Z 0) ≠ 0 := by
  rw [gaussianPairing_inner, inner_self_ne_zero]
  intro h
  have hf : AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.realSiegelGaussian Z 0 = 0 := (Weil.Local.UnitaryInner.Construction.testToL2_injective ℝ N) (h.trans (map_zero _).symm)
  have hv := congrArg (fun f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N => f.val 0) hf
  rw [AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.real_siegel_gaussian_at_zero] at hv
  exact one_ne_zero hv

theorem gaussianPairing_continuous {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (Z : X → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (hZ : Continuous (fun x => (Z x).matrix))
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) : Continuous (fun x => gaussianPairing (Z x) f) := by
  apply continuous_of_dominated
    (bound := fun y => ‖f.val y‖)
  · intro x
    exact ((Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat_continuous (AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.realSiegelGaussian (Z x) 0).property).mul
      ((Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat_continuous f.property).star)).aestronglyMeasurable
  · intro x
    apply Filter.Eventually.of_forall
    intro y
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_right (real_gaussian_norm_le_one (Z x) y) (norm_nonneg _)).trans_eq (one_mul _)
  · exact (Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat_integrable (Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ N) f).norm
  · apply Filter.Eventually.of_forall
    intro y
    apply Continuous.mul _ continuous_const
    simp only [AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient.CM.real_siegel_gaussian_apply, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
    fun_prop

end

end OAI.RepresentationTheory.Theta.Adelic.GaussianWeakContinuity
