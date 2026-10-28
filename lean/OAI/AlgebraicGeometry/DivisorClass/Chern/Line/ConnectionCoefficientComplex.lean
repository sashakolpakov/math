import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorGradientCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergyExpansion
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorCurvature

/-! # Connection Coefficient Complex -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionCoefficientComplex

noncomputable section

section

/-! The original lower-order line connection as an explicit continuous matrix from fiber values to all physical gradient coordinates. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  CovectorConnectionOperator.lineOperator_formNormed CovectorConnectionOperator.lineOperator_formSpace CovectorConnectionOperator.lineOperator_endNormed CovectorConnectionOperator.lineOperator_endSpace

variable {E D ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

def lineGradientConnectionCoefficient (b : Module.Basis ι ℝ E) (n : ℕ)
    (G : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] ℂ) :
    OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates ι n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).comp
      ((CovectorConnectionOperator.lineCovectorConnectionOperator n G A (b i)).comp
        ((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm.toContinuousLinearMap.restrictScalars ℝ))))

theorem lineGradientConnectionCoefficient_tensor (b : Module.Basis ι ℝ E) (n : ℕ)
    (G : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] ℂ) (v : OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) :
    GradientTensorCoordinates.covectorGradientTensor b n (lineGradientConnectionCoefficient b n G A v) =
      EnergyExpansion.lineCovectorConnectionValueTensor n G A ((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm v) := by
  have hc : lineGradientConnectionCoefficient b n G A v =
      TensorGradientCoordinates.covectorTensorGradientCoordinates b n (EnergyExpansion.lineCovectorConnectionValueTensor n G A ((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm v)) := by
    apply PiLp.ext
    intro i
    rfl
  exact (congrArg (GradientTensorCoordinates.covectorGradientTensor b n) hc).trans (TensorGradientCoordinates.covectorGradientTensor_left_inverse b n _)

theorem lineGradientConnectionCoefficient_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (G : D → E →L[ℝ] E →L[ℝ] E) (A : D → E →L[ℝ] ℂ) {U : Set D}
    (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun x => lineGradientConnectionCoefficient b n (G x) (A x)) U := by
  have hrow (i : ι) : ContDiffOn ℝ ∞ (fun x => CovectorConnectionOperator.lineCovectorConnectionOperator n (G x) (A x) (b i)) U :=
    (((contDiffOn_const (c := CovectorConnectionOperator.covectorActionOperator (E := E) n)).clm_apply (hG.clm_apply contDiffOn_const)).neg).add
      ((contDiffOn_const (c := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E n))).clm_apply (hA.clm_apply contDiffOn_const))
  apply contDiffOn_clm_apply.mpr
  intro v
  apply (contDiffOn_piLp 2).mpr
  intro i
  exact ((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
    ((hrow i).clm_apply contDiffOn_const)

theorem lineCovectorConnectionDerivative_gradient_coordinates (b : Module.Basis ι ℝ E) (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    GradientTensorCoordinates.covectorGradientTensor b n (TensorGradientCoordinates.covectorTensorGradientCoordinates b n (fderiv ℝ a x) +
      lineGradientConnectionCoefficient b n (G x) (A x) (OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (a x))) =
      ConnectionSymbols.lineCovectorConnectionDerivative n G A a x := by
  rw [map_add, TensorGradientCoordinates.covectorGradientTensor_left_inverse, lineGradientConnectionCoefficient_tensor,
    ContinuousLinearEquiv.symm_apply_apply]
  exact (EnergyExpansion.lineCovectorConnectionDerivative_tensor_split n G A a x).symm

end

/-! The literal lower-order connection matrix commutes with the original complex scalar multiplication. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  CovectorConnectionOperator.lineOperator_formNormed CovectorConnectionOperator.lineOperator_formSpace CovectorConnectionOperator.lineOperator_endNormed CovectorConnectionOperator.lineOperator_endSpace

theorem lineCovectorConnectionOperator_complex_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (G : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] ℂ) (v : E) (r : ℂ) (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    CovectorConnectionOperator.lineCovectorConnectionOperator n G A v (r • a) = r • CovectorConnectionOperator.lineCovectorConnectionOperator n G A v a := by
  rw [CovectorConnectionOperator.lineCovectorConnectionOperator_apply, CovectorConnectionOperator.lineCovectorConnectionOperator_apply,
    OneCovectorCurvature.covectorInfinitesimalAction_complex_smul, smul_add, smul_neg, smul_comm (A v) r a]

theorem lineGradientConnectionCoefficient_complex_smul {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [LinearOrder ι]
    (b : Module.Basis ι ℝ E) (n : ℕ) (G : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] ℂ)
    (r : ℂ) (a : OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) :
    lineGradientConnectionCoefficient b n G A (r • a) = r • lineGradientConnectionCoefficient b n G A a := by
  apply PiLp.ext
  intro j
  change OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n
      (CovectorConnectionOperator.lineCovectorConnectionOperator n G A (b j) ((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (r • a))) =
    r • OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n
      (CovectorConnectionOperator.lineCovectorConnectionOperator n G A (b j) ((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm a))
  rw [map_smul, lineCovectorConnectionOperator_complex_smul, map_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionCoefficientComplex
