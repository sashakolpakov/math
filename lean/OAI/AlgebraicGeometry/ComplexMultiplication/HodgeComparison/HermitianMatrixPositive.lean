import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation
import OAI.Analysis.HodgeTheory.Decomposition.MetricFiber
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! # Hermitian Matrix Positive -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianMatrixPositive.CM.Construction

noncomputable section

/-! Positive definiteness of the actual Hermitian metric matrix in a complex basis. -/

open scoped ComplexOrder

theorem varietyHermitianMatrix_eq_gram (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} (v : ι → V.analyticModel) {y : V.analyticModel} (hy : y ∈ e.target) :
    InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e v y = Matrix.gram ℂ
      (fun i => (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm (v i)) := by
  ext i j
  rw [Matrix.gram_apply, OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiber_inner]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem varietyHermitianMatrix_posDef (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} [Finite ι] (v : Module.Basis ι ℂ V.analyticModel)
    {y : V.analyticModel} (hy : y ∈ e.target) :
    (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e v y).PosDef := by
  rw [varietyHermitianMatrix_eq_gram V e he v hy]
  exact Matrix.posDef_gram_of_linearIndependent
    (v.map (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm.toLinearEquiv).linearIndependent

theorem varietyHermitianMatrix_det_isUnit (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Module.Basis ι ℂ V.analyticModel)
    {y : V.analyticModel} (hy : y ∈ e.target) :
    IsUnit (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e v y).det :=
  isUnit_iff_ne_zero.mpr (varietyHermitianMatrix_posDef V e he v hy).det_pos.ne'

theorem varietyHermitianMatrix_differentiableAt (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} (v : ι → V.analyticModel) {y : V.analyticModel} (hy : y ∈ e.target) (i j : ι) :
    DifferentiableAt ℝ (fun z => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e v z i j) y :=
  ((OAI.Analysis.HodgeTheory.Decomposition.Hermitian.Constructions.projectiveMetricHermitian_smooth V e he (v i) (v j)).contDiffAt
    (e.open_target.mem_nhds hy)).differentiableAt (by simp)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianMatrixPositive.CM.Construction
