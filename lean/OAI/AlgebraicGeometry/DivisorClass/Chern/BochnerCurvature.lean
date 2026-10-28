import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Bochner
import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedCurvatureNorm

/-! # Bochner Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.BochnerCurvature

noncomputable section

/-! The exact zeroth-order curvature operator in the original full real Bochner formula. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace Line.CurvatureNorm.curvatureNorm_formComplex

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def fullBochnerCurvatureAction (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  BaseCurvatureAction.baseCurvatureAction b B G x a + Line.CurvatureContraction.lineCurvatureAction b B F a -
    (Complex.I / 4) • Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 B (OperatorConnectionCurvature.operatorConnectionCurvature G x) F a

theorem fullBochnerCurvatureAction_norm_of_bounds (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (C D : ℝ)
    (hbase : ‖BaseCurvatureAction.baseCurvatureAction b B G x a‖ ≤ C * ‖a‖)
    (hline : ‖Line.CurvatureContraction.lineCurvatureAction b B F a‖ ≤ D * ‖a‖)
    (hmix : ‖Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 B (OperatorConnectionCurvature.operatorConnectionCurvature G x) F a‖ ≤ D * ‖a‖) :
    ‖fullBochnerCurvatureAction b B G x F a‖ ≤ (C + 2 * D) * ‖a‖ := by
  have hcoef : ‖(Complex.I / 4 : ℂ)‖ ≤ 1 := by norm_num
  have hc : ‖(Complex.I / 4) • Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 B (OperatorConnectionCurvature.operatorConnectionCurvature G x) F a‖ ≤ D * ‖a‖ := by
    rw [norm_smul]
    exact ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans_eq (one_mul _)).trans hmix
  have hn := norm_sub_le (BaseCurvatureAction.baseCurvatureAction b B G x a + Line.CurvatureContraction.lineCurvatureAction b B F a)
    ((Complex.I / 4) • Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 B (OperatorConnectionCurvature.operatorConnectionCurvature G x) F a)
  have ha := norm_add_le (BaseCurvatureAction.baseCurvatureAction b B G x a) (Line.CurvatureContraction.lineCurvatureAction b B F a)
  change ‖BaseCurvatureAction.baseCurvatureAction b B G x a + Line.CurvatureContraction.lineCurvatureAction b B F a -
    (Complex.I / 4) • Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 B (OperatorConnectionCurvature.operatorConnectionCurvature G x) F a‖ ≤ _
  nlinarith only [hn, ha, hbase, hline, hc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.BochnerCurvature
