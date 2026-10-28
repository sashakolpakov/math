import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoefficient
import OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift

/-! # Gradient Coefficient Complex -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GradientCoefficientComplex

noncomputable section

/-! The actual physical principal coefficient is complex-linear on all finite Hilbert gradient coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem covectorGradientComponent_complex_smul (n : ℕ) (j : ι) (r : ℂ) (v : GradientTensorCoordinates.CovectorGradientCoordinates ι n) :
    GradientTensorCoordinates.covectorGradientComponent n j (r • v) = r • GradientTensorCoordinates.covectorGradientComponent n j v := rfl

theorem covectorGradientCoefficient_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (w : ℝ) (r : ℂ) (v : GradientTensorCoordinates.CovectorGradientCoordinates ι n) :
    GradientTensorCoefficient.covectorGradientCoefficient b n B w (r • v) = r • GradientTensorCoefficient.covectorGradientCoefficient b n B w v := by
  simp only [GradientTensorCoefficient.covectorGradientCoefficient, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covectorGradientComponent_complex_smul, Analysis.HodgeTheory.Decomposition.ComplexMetric.Constructions.realMatrixOperator_complex_smul,
    Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions.real_adjoint_complex_smul (GradientTensorCoordinates.covectorGradientComponent n i) (covectorGradientComponent_complex_smul n i)]
  exact smul_comm _ r _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GradientCoefficientComplex
