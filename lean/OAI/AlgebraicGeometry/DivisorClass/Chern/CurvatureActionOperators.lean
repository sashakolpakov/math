import OAI.AlgebraicGeometry.DivisorClass.Chern.BochnerCurvature

/-! # Curvature Action Operators -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureActionOperators

noncomputable section

/-! Every term of the actual full Bochner curvature remainder is a bounded linear operator on the original one-covector fiber. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace Line.CurvatureNorm.curvatureNorm_formComplex
  BaseCurvatureAction.baseAction_endNormed BaseCurvatureAction.baseAction_endSpace BaseCurvatureAction.baseAction_directionNormed BaseCurvatureAction.baseAction_directionSpace
  Line.CurvatureNorm.curvatureNorm_covectorNormed Line.CurvatureNorm.curvatureNorm_covectorSpace Line.CurvatureNorm.curvatureNorm_covectorComplex

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

def baseCurvatureContractionCLM (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] E →L[ℝ] ℂ :=
  -∑ i, (((ContinuousLinearMap.compL ℝ E E ℂ).flip
    ((ContinuousLinearMap.apply ℝ E (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)).comp
      (OperatorConnectionCurvature.operatorConnectionCurvatureRight G x (b i)))).comp AntiOneFormCoordinates.oneFormLinearEquiv.symm.toContinuousLinearMap)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem baseCurvatureContractionCLM_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    baseCurvatureContractionCLM b B G x a = BaseCurvatureAction.baseCurvatureContraction b B G x a := by
  simp only [baseCurvatureContractionCLM, _root_.neg_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  rfl

def baseCurvatureActionCLM (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  AntiOneFormCoordinates.oneFormLinearEquiv.toContinuousLinearMap.comp
    (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ).restrictScalars ℝ).comp (baseCurvatureContractionCLM b B G x))

theorem baseCurvatureActionCLM_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    baseCurvatureActionCLM b B G x a = BaseCurvatureAction.baseCurvatureAction b B G x a := by
  change AntiOneFormCoordinates.oneFormLinearEquiv (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (baseCurvatureContractionCLM b B G x a)) = _
  rw [baseCurvatureContractionCLM_apply]
  rfl

def lineCurvatureContractionCLM (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] E →L[ℝ] ℂ :=
  ∑ i, (((ContinuousLinearMap.lsmul ℝ ℂ).flip (AntiTwoFormCoefficients.twoFormBilinear F (b i))).comp
    ((ContinuousLinearMap.apply ℝ ℂ (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)).comp
      AntiOneFormCoordinates.oneFormLinearEquiv.symm.toContinuousLinearMap))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem lineCurvatureContractionCLM_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    lineCurvatureContractionCLM b B F a = Line.CurvatureContraction.lineCurvatureContraction b B F a := by
  simp only [lineCurvatureContractionCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.apply_apply]
  rfl

def lineCurvatureActionCLM (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  AntiOneFormCoordinates.oneFormLinearEquiv.toContinuousLinearMap.comp
    (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ).restrictScalars ℝ).comp (lineCurvatureContractionCLM b B F))

theorem lineCurvatureActionCLM_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    lineCurvatureActionCLM b B F a = Line.CurvatureContraction.lineCurvatureAction b B F a := by
  change AntiOneFormCoordinates.oneFormLinearEquiv (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (lineCurvatureContractionCLM b B F a)) = _
  rw [lineCurvatureContractionCLM_apply]
  rfl

def lineMixedCurvatureTraceCLM (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (R : E → E → E →L[ℝ] E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  ∑ i, (-Line.CovectorConnectionOperator.covectorActionOperator 1 (R (b i) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)) +
    F ![b i, Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap] • ContinuousLinearMap.id ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E 1))

omit [IsScalarTower ℝ ℂ E] in
theorem lineMixedCurvatureTraceCLM_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (R : E → E → E →L[ℝ] E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    lineMixedCurvatureTraceCLM b B R F a = Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 B R F a := by
  simp only [lineMixedCurvatureTraceCLM, Line.RoughAnti.lineCovectorMixedCurvatureTrace, _root_.sum_apply,
    _root_.add_apply, _root_.neg_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
    Line.CovectorConnectionOperator.covectorActionOperator_apply]

def fullBochnerCurvatureCLM (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  baseCurvatureActionCLM b B G x + lineCurvatureActionCLM b B F -
    (Complex.I / 4) • lineMixedCurvatureTraceCLM b B (OperatorConnectionCurvature.operatorConnectionCurvature G x) F

theorem fullBochnerCurvatureCLM_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    fullBochnerCurvatureCLM b B G x F a = BochnerCurvature.fullBochnerCurvatureAction b B G x F a := by
  simp only [fullBochnerCurvatureCLM, BochnerCurvature.fullBochnerCurvatureAction, _root_.add_apply, _root_.sub_apply,
    _root_.smul_apply, baseCurvatureActionCLM_apply, lineCurvatureActionCLM_apply, lineMixedCurvatureTraceCLM_apply]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureActionOperators
