import OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureActionOperators
import OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorCurvatureSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorSmooth

/-! # Curvature Action Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureActionSmooth

noncomputable section

/-! Every coefficient of the original full Bochner curvature remainder varies smoothly on a genuine positive metric chart. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace Line.CurvatureNorm.curvatureNorm_formComplex
  BaseCurvatureAction.baseAction_endNormed BaseCurvatureAction.baseAction_endSpace BaseCurvatureAction.baseAction_directionNormed BaseCurvatureAction.baseAction_directionSpace
  Line.CurvatureNorm.curvatureNorm_covectorNormed Line.CurvatureNorm.curvatureNorm_covectorSpace Line.CurvatureNorm.curvatureNorm_covectorComplex
  Line.CurvatureNorm.curvatureNorm_twoNormed Line.CurvatureNorm.curvatureNorm_twoSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem baseCurvatureContraction_smoothOn (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (ha : ContDiffOn ℝ ∞ a U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => BaseCurvatureAction.baseCurvatureContraction b (B x) G x (a x)) U := by
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hq := (AntiOneFormCoordinates.oneFormLinearEquiv (E := E)).symm.toContinuousLinearMap.contDiff.comp_contDiffOn ha
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro i _
  have hR := OperatorCurvatureSmooth.operatorConnectionCurvatureRight_smoothOn G (fun _ => b i) hU hG contDiffOn_const
  have hL : ContDiffOn ℝ ∞ (fun x =>
      (ContinuousLinearMap.apply ℝ E (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)).comp
        (OperatorConnectionCurvature.operatorConnectionCurvatureRight G x (b i))) U := by
    apply contDiffOn_clm_apply.mpr
    intro v
    have hRv : ContDiffOn ℝ ∞ (fun x => OperatorConnectionCurvature.operatorConnectionCurvatureRight G x (b i) v) U :=
      hR.clm_apply (contDiffOn_const (c := v))
    have hSi : ContDiffOn ℝ ∞ (fun x => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) U :=
      hS.clm_apply (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
    exact hRv.clm_apply hSi
  exact hq.clm_comp hL

local instance curvatureAction_dualNormed : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance curvatureAction_dualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance curvatureAction_sharpNormed : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
local instance curvatureAction_sharpSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem baseCurvatureAction_smoothOn (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (ha : ContDiffOn ℝ ∞ a U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => BaseCurvatureAction.baseCurvatureAction b (B x) G x (a x)) U :=
  (AntiOneFormCoordinates.oneFormLinearEquiv (E := E)).toContinuousLinearMap.contDiff.comp_contDiffOn
    (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn
      (baseCurvatureContraction_smoothOn b B G a hU hB hG ha hpos))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem lineCurvatureContraction_smoothOn (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (F : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hF : ContDiffOn ℝ ∞ F U) (ha : ContDiffOn ℝ ∞ a U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => Line.CurvatureContraction.lineCurvatureContraction b (B x) (F x) (a x)) U := by
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hq := (AntiOneFormCoordinates.oneFormLinearEquiv (E := E)).symm.toContinuousLinearMap.contDiff.comp_contDiffOn ha
  have hT : ContDiffOn ℝ ∞ (fun x => AntiTwoFormCoefficients.twoFormBilinear (F x)) U := by
    have ht := (ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear (E := E)).contDiff.comp_contDiffOn hF
    exact ht.congr (fun x _ => Line.CurvatureNorm.twoFormBilinear_eq_native (F x))
  apply ContDiffOn.sum
  intro i _
  exact (hq.clm_apply (hS.clm_apply contDiffOn_const)).smul (hT.clm_apply contDiffOn_const)

theorem lineCurvatureAction_smoothOn (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (F : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hF : ContDiffOn ℝ ∞ F U) (ha : ContDiffOn ℝ ∞ a U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => Line.CurvatureContraction.lineCurvatureAction b (B x) (F x) (a x)) U :=
  (AntiOneFormCoordinates.oneFormLinearEquiv (E := E)).toContinuousLinearMap.contDiff.comp_contDiffOn
    (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn
      (lineCurvatureContraction_smoothOn b B F a hU hB hF ha hpos))

theorem lineMixedCurvatureTrace_smoothOn
    {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (F : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U)
    (hF : ContDiffOn ℝ ∞ F U) (ha : ContDiffOn ℝ ∞ a U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => Line.RoughAnti.lineCovectorMixedCurvatureTrace b 1 (B x)
      (OperatorConnectionCurvature.operatorConnectionCurvature G x) (F x) (a x)) U := by
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hT := (ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear (E := E)).contDiff.comp_contDiffOn hF
  apply ContDiffOn.sum
  intro i _
  have hSi := hS.clm_apply (𝕜 := ℝ) (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
  have hJ : ContDiffOn ℝ ∞ (fun x => Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) U :=
    hSi.const_smul Complex.I
  have hR := OperatorCurvatureSmooth.operatorConnectionCurvature_smoothOn G (fun _ => b i) _ hU hG contDiffOn_const hJ
  have hC := (Line.CovectorConnectionOperator.covectorActionOperator (E := E) 1).contDiff.comp_contDiffOn hR
  have hCa := hC.clm_apply ha
  have hFa := (hT.clm_apply (contDiffOn_const (c := b i))).clm_apply hJ
  have hrow := hCa.neg.add (hFa.smul ha)
  apply hrow.congr
  intro x _
  exact congrArg₂ (fun (q : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (t : ℂ) => -q + t • a x)
    (Line.CovectorConnectionOperator.covectorActionOperator_apply 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x (b i)
      (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) (a x)).symm
    (ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply (F x) (b i)
      (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)).symm

theorem fullBochnerCurvatureAction_smoothOn (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (F : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U)
    (hF : ContDiffOn ℝ ∞ F U) (ha : ContDiffOn ℝ ∞ a U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => BochnerCurvature.fullBochnerCurvatureAction b (B x) G x (F x) (a x)) U :=
  ((baseCurvatureAction_smoothOn b B G a hU hB hG ha hpos).add
    (lineCurvatureAction_smoothOn b B F a hU hB hF ha hpos)).sub
      ((lineMixedCurvatureTrace_smoothOn b B G F a hU hB hG hF ha hpos).const_smul (Complex.I / 4))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureActionSmooth
