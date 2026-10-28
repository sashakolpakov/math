import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.ProductBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CutoffSymbolMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffOne

/-! # Cutoff Integral Bounds -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Pointwise original bundle metric bounds for cutoff multiplication in the joint Dolbeault energy. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace Projective.BaseActionBounds.baseBound_sharpNormed Projective.BaseActionBounds.baseBound_sharpSpace
  Projective.BaseMetricBounds.basePair_metricNormed Projective.BaseMetricBounds.basePair_metricSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he hs

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_point_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (x : V.analyticSpace),
      let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
      (h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val x).re ≤
        C * (h.globalFormPair V 1 a.val a.val x).re +
          D * (h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val x).re ∧
      (h.globalFormPair V 0 (h.degreeCodifferential V 0 A.val) (h.degreeCodifferential V 0 A.val) x).re ≤
        C * (h.globalFormPair V 1 a.val a.val x).re +
          D * (h.globalFormPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 a.val) x).re := by
  let T := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport f
  have hT : IsCompact T := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e (isClosed_tsupport f).isCompact (fun _ hx => (hs hx).1)
  have hTD := HolomorphicCompact.ChartField.holomorphicLineCutoff_image_domain V e i f hs
  have hbound := Projective.CutoffSymbolMetric.projectiveCutoffSymbols_metric_bound V e he f hf hT (fun _ hz => (hTD hz).1)
  let C := hbound.choose
  have hC := hbound.choose_spec.1
  have hb := hbound.choose_spec.2
  have hscalar := Holomorphic.CutoffCoordinates.smoothComplexFunction_norm_sq_bound V f hf
  let K := hscalar.choose
  have hK := hscalar.choose_spec.1
  have hKb := hscalar.choose_spec.2
  refine ⟨2 * C, 2 * K, mul_pos (by norm_num) hC, mul_pos (by norm_num) hK, fun a x => ?_⟩
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  by_cases hx : x ∈ tsupport f
  · let z := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x
    have hzT : z ∈ T := ⟨x, hx, rfl⟩
    have hz := hTD hzT
    have heq : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z = x := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (hs hx).1
    have hg : ‖f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)‖ ^ 2 ≤ K := by rw [heq]; exact hKb x
    have hD := h.globalFormPair_bound_of_chart_product V e he i 2 a.val
      (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val hz
      (Line.Cutoff.lineDolbeaultCutoffSymbol 1 (fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z)) (f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) C K
      (h.cutoffDolbeault_covector V e he i f hf a hz) (hb z hzT (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z)).1 hg
    have hS := h.globalFormPair_bound_of_chart_product V e he i 0 a.val
      (h.degreeCodifferential V 0 A.val) (h.degreeCodifferential V 0 a.val) hz
      (Line.Cutoff.lineCodifferentialCutoffSymbol (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z)
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z)) (f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) C K
      (h.cutoffCodifferential_covector V e he i f hf a hz) (hb z hzT (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z)).2 hg
    exact Eq.mp (congrArg (fun y : V.analyticSpace =>
      (h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val y).re ≤
        (2 * C) * (h.globalFormPair V 1 a.val a.val y).re +
          (2 * K) * (h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val y).re ∧
      (h.globalFormPair V 0 (h.degreeCodifferential V 0 A.val) (h.degreeCodifferential V 0 A.val) y).re ≤
        (2 * C) * (h.globalFormPair V 1 a.val a.val y).re +
          (2 * K) * (h.globalFormPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 a.val) y).re) heq) ⟨hD, hS⟩
  · have hz := h.cutoff_operators_pair_zero V f hf a x hx
    exact ⟨(congrArg Complex.re hz.1).trans_le
      (add_nonneg (mul_nonneg (mul_pos (by norm_num) hC).le (h.globalFormPair_nonneg V 1 a.val x))
        (mul_nonneg (mul_pos (by norm_num) hK).le (h.globalFormPair_nonneg V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val x))),
      (congrArg Complex.re hz.2).trans_le
        (add_nonneg (mul_nonneg (mul_pos (by norm_num) hC).le (h.globalFormPair_nonneg V 1 a.val x))
          (mul_nonneg (mul_pos (by norm_num) hK).le (h.globalFormPair_nonneg V 0 (h.degreeCodifferential V 0 a.val) x)))⟩

end

/-! Integrated original Dolbeault and codifferential bounds for actual smooth cutoffs. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_bound_of_point (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (c d : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (C D : ℝ)
    (hp : ∀ x, (h.globalFormPair V n c c x).re ≤
      C * (h.globalFormPair V 1 a a x).re + D * (h.globalFormPair V n d d x).re) :
    (h.formIntegralPair V n c c).re ≤ C * (h.formIntegralPair V 1 a a).re + D * (h.formIntegralPair V n d d).re := by
  have hA : Integrable (fun x => C * (h.globalFormPair V 1 a a x).re) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
    (h.globalFormPair_integrable V 1 a a).re.const_mul C
  have hD : Integrable (fun x => D * (h.globalFormPair V n d d x).re) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
    (h.globalFormPair_integrable V n d d).re.const_mul D
  calc
    _ = ∫ x, (h.globalFormPair V n c c x).re ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := h.formIntegralPair_re V n c c
    _ ≤ ∫ x, (C * (h.globalFormPair V 1 a a x).re + D * (h.globalFormPair V n d d x).re) ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      integral_mono (h.globalFormPair_integrable V n c c).re (hA.add hD) hp
    _ = _ := by
      rw [integral_add hA hD, integral_const_mul, integral_const_mul]
      exact congrArg₂ (fun r s : ℝ => C * r + D * s)
        (h.formIntegralPair_re V 1 a a).symm (h.formIntegralPair_re V n d d).symm

variable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he hs

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_integral_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
      (h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val).re ≤
        C * (h.formIntegralPair V 1 a.val a.val).re +
          D * (h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val).re ∧
      (h.formIntegralPair V 0 (h.degreeCodifferential V 0 A.val) (h.degreeCodifferential V 0 A.val)).re ≤
        C * (h.formIntegralPair V 1 a.val a.val).re +
          D * (h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 a.val)).re := by
  have H := h.cutoff_operators_point_bound V e he i f hf hs
  let C := H.choose
  let D := H.choose_spec.choose
  have hCD := H.choose_spec.choose_spec
  refine ⟨C, D, hCD.1, hCD.2.1, fun a => ?_⟩
  exact ⟨h.formIntegralPair_bound_of_point V 2 a.val
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val C D (fun x => (hCD.2.2 a x).1),
    h.formIntegralPair_bound_of_point V 0 a.val
      (h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val)
      (h.degreeCodifferential V 0 a.val) C D (fun x => (hCD.2.2 a x).2)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
