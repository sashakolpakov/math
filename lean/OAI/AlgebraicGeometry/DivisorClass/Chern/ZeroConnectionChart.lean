import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative

/-! # Zero Connection Chart -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroConnectionChart

noncomputable section

/-! The original section connection has the exact exterior-symbol formula, including the degree-zero boundary. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section ZeroSymbol
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem alternation_lineConnectionTerm_zero (A : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 0) :
    alternatizeUncurryFin (Line.ConnectionSymbols.lineConnectionTerm 0 (AntiOneFormCoordinates.oneFormLinear A) a) = a 0 • A := by
  ext v
  rw [alternatizeUncurryFin_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, Line.ConnectionSymbols.lineConnectionTerm_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, AntiOneFormCoordinates.oneFormLinear_apply]
  have hv : (fun _ : Fin 1 => v 0) = v := by funext i; fin_cases i; rfl
  have ha : (Fin.removeNth (0 : Fin 1) v) = 0 := Subsingleton.elim _ _
  rw [hv, ha]
  exact mul_comm _ _
end ZeroSymbol

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (U : Opens V.analyticSpace)

theorem projectiveOpenChartForm_add (n : ℕ) (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a + b).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.extension z + Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n b.extension z := by
  simp only [Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply]
  ext v
  rfl

theorem projectiveOpenChartForm_zero_mul (n : ℕ) (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 0) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (SmoothScalarExterior.openZeroFormMul A a).extension z =
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 a.extension z) 0 • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n A.extension z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩,
    SmoothScalarExterior.openZeroFormMul_apply,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply a ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply A ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  congr 1
  congr 1
  exact Subsingleton.elim _ _

include he

theorem projectiveOpenChartForm_connectionZero (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 0) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (SmoothScalarExterior.openConnectionDerivative A a).extension z =
      Line.ConnectionSymbols.lineExteriorDerivative 0 (fun y => AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 A.extension y))
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 a.extension) z := by
  change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a + SmoothScalarExterior.openZeroFormMul A a).extension z = _
  rw [projectiveOpenChartForm_add, ConnectionChartDerivative.projectiveOpenChartForm_d V e he U 0 a hz,
    projectiveOpenChartForm_zero_mul V e U 1 A a hz, Line.ConnectionSymbols.lineExteriorDerivative,
    alternation_lineConnectionTerm_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroConnectionChart
