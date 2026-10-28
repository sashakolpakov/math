import OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureActionOperators

/-! # Curvature Complex -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureComplex

noncomputable section

/-! Every term of the full original Bochner curvature action is complex-linear in its covector argument. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace Line.CurvatureNorm.curvatureNorm_formComplex
  BaseCurvatureAction.baseAction_endNormed BaseCurvatureAction.baseAction_endSpace BaseCurvatureAction.baseAction_directionNormed BaseCurvatureAction.baseAction_directionSpace
  Line.CurvatureNorm.curvatureNorm_covectorNormed Line.CurvatureNorm.curvatureNorm_covectorSpace Line.CurvatureNorm.curvatureNorm_covectorComplex

theorem oneFormLinearEquiv_smul_value {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] ℂ) (r : ℂ) : AntiOneFormCoordinates.oneFormLinearEquiv (r • a) = r • AntiOneFormCoordinates.oneFormLinearEquiv a := by
  ext v
  rfl

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]

theorem baseCurvatureContraction_complex_smul (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (r : ℂ) :
    BaseCurvatureAction.baseCurvatureContraction b B G x (r • a) = r • BaseCurvatureAction.baseCurvatureContraction b B G x a := by
  ext v
  simp only [BaseCurvatureAction.baseCurvatureContraction_apply, OneCovectorCurvature.covectorInfinitesimalAction_complex_smul,
    ContinuousAlternatingMap.smul_apply, _root_.smul_apply, Finset.smul_sum, smul_neg]

theorem lineCurvatureContraction_complex_smul (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (r : ℂ) :
    Line.CurvatureContraction.lineCurvatureContraction b B F (r • a) = r • Line.CurvatureContraction.lineCurvatureContraction b B F a := by
  ext v
  simp only [Line.CurvatureContraction.lineCurvatureContraction_apply, AntiOneFormCoordinates.oneFormLinear_apply, ContinuousAlternatingMap.smul_apply,
    _root_.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem baseCurvatureAction_complex_smul (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (r : ℂ) :
    BaseCurvatureAction.baseCurvatureAction b B G x (r • a) = r • BaseCurvatureAction.baseCurvatureAction b B G x a := by
  rw [BaseCurvatureAction.baseCurvatureAction, BaseCurvatureAction.baseCurvatureAction, baseCurvatureContraction_complex_smul,
    map_smul, oneFormLinearEquiv_smul_value]

theorem lineCurvatureAction_complex_smul (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (r : ℂ) :
    Line.CurvatureContraction.lineCurvatureAction b B F (r • a) = r • Line.CurvatureContraction.lineCurvatureAction b B F a := by
  rw [Line.CurvatureContraction.lineCurvatureAction, Line.CurvatureContraction.lineCurvatureAction, lineCurvatureContraction_complex_smul,
    map_smul, oneFormLinearEquiv_smul_value]

omit [IsScalarTower ℝ ℂ E] in
theorem lineCovectorMixedCurvatureTrace_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (R : E → E → E →L[ℝ] E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (r : ℂ) :
    Line.RoughAnti.lineCovectorMixedCurvatureTrace b n B R F (r • a) = r • Line.RoughAnti.lineCovectorMixedCurvatureTrace b n B R F a := by
  simp only [Line.RoughAnti.lineCovectorMixedCurvatureTrace, OneCovectorCurvature.covectorInfinitesimalAction_complex_smul,
    Finset.smul_sum, smul_add, smul_neg]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : Analysis.DifferentialForms.Manifold.Basic.FormValue E n =>
    -(r • Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (R (b j) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)) a) + v)
    (smul_comm _ r a)

theorem fullBochnerCurvatureAction_complex_smul (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (r : ℂ) :
    BochnerCurvature.fullBochnerCurvatureAction b B G x F (r • a) = r • BochnerCurvature.fullBochnerCurvatureAction b B G x F a := by
  rw [BochnerCurvature.fullBochnerCurvatureAction, BochnerCurvature.fullBochnerCurvatureAction, baseCurvatureAction_complex_smul,
    lineCurvatureAction_complex_smul, lineCovectorMixedCurvatureTrace_complex_smul, smul_sub, smul_add,
    smul_comm (Complex.I / 4) r]

theorem fullBochnerCurvatureCLM_complex_smul (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (r : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    CurvatureActionOperators.fullBochnerCurvatureCLM b B G x F (r • a) = r • CurvatureActionOperators.fullBochnerCurvatureCLM b B G x F a := by
  rw [CurvatureActionOperators.fullBochnerCurvatureCLM_apply, CurvatureActionOperators.fullBochnerCurvatureCLM_apply, fullBochnerCurvatureAction_complex_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureComplex
