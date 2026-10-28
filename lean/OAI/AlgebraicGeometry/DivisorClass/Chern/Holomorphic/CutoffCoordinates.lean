import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Cutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.Bochner
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral

/-! # Cutoff Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Exact coordinate product rules for the original global bundle cutoff forms. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open _root_.ContinuousAlternatingMap

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)

theorem Holomorphic.CutoffCoordinates.holomorphicLineSmoothMul_covector (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a).val i).extension z =
      f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Holomorphic.AntiMultiplication.holomorphicLineSmoothMul_inChart u ⊤ f hf n a i e ⟨trivial, hz.2⟩]
  ext v
  rfl

theorem Holomorphic.CutoffCoordinates.holomorphicLineSmoothMul_eventually_covector (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a).val i).extension =ᶠ[𝓝 z]
      fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y) • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension y := by
  filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz] with y hy
  exact Holomorphic.CutoffCoordinates.holomorphicLineSmoothMul_covector V e i f hf n a hy

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothMul_covariant_tensor (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let g := fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)
    let c := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension
    Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a).val i).extension) z =
      Line.ConnectionSymbols.lineConnectionTerm n (fderiv ℝ g z) (c z) + g z • Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A c z := by
  have heq := Holomorphic.CutoffCoordinates.holomorphicLineSmoothMul_eventually_covector V e i f hf n a hz
  have hg := ((Projective.GlobalPairSmooth.projectiveGlobalScalar_smooth V e he f hf).contDiffAt
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz.1)).differentiableAt (by simp)
  have ha := ((ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he
    (⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) n (a.val i)).contDiffAt
      ((ConnectionChartDerivative.projectiveOpenChartDomain V e (⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds
        ⟨hz.1, trivial, hz.2⟩)).differentiableAt (by simp)
  exact (Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr n _ _ _ _ heq).trans
    (Line.Cutoff.lineCovectorConnectionDerivative_scalar_tensor n _ _ _ _ hg ha)

include h in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoffDolbeault_covector (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val.val i).extension z =
      Line.Cutoff.lineDolbeaultCutoffSymbol 1 (fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z) + f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) •
          Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val.val i).extension z := by
  have hA := h.projectiveDolbeault_covariant V e he ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a) i ⟨hz.1, trivial, hz.2⟩
  have ha := h.projectiveDolbeault_covariant V e he ⊤ 1 a i ⟨hz.1, trivial, hz.2⟩
  have ht := h.smoothMul_covariant_tensor V e he i f hf 1 a.val hz
  have hp := congrArg (fun N : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 =>
    alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) N)) ht
  apply hA.trans (hp.trans ?_)
  exact (Line.Cutoff.lineDolbeaultCutoffSymbol_add_tensor 1 _ _ _ _).trans
    (congrArg (fun r : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 2 =>
      Line.Cutoff.lineDolbeaultCutoffSymbol 1 (fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z) + f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • r) ha.symm)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoffCodifferential_covector (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val).val i).extension z =
      Line.Cutoff.lineCodifferentialCutoffSymbol (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z) + f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) •
          Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension z := by
  rw [h.degreeCodifferential_covector V e he i (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a) hz,
    h.degreeCodifferential_covector V e he i a hz]
  dsimp only [HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm]
  unfold Line.ConnectionSymbols.lineCovariantCodifferential Line.Cutoff.lineCodifferentialCutoffSymbol
  rw [h.smoothMul_covariant_tensor V e he i f hf 1 a.val hz]
  simp only [_root_.add_apply, _root_.smul_apply, Line.ConnectionSymbols.lineConnectionTerm_apply,
    map_add, Line.ConnectionSymbols.exteriorContraction_complex_smul, Finset.sum_add_distrib, ← Finset.smul_sum, smul_neg]
  exact neg_add _ _

end

/-! The exact original metric norm of smooth bundle multiplication and its compactness bound. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Holomorphic.CutoffCoordinates.complex_weighted_smul_self_re (w g p : ℂ) :
    (w * (conj g * (g * p))).re = ‖g‖ ^ 2 * (w * p).re := by
  have he : w * (conj g * (g * p)) = (Complex.normSq g : ℂ) * (w * p) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_smoothMul_self (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    (h.globalFormPair V n (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) x).re =
      ‖f x‖ ^ 2 * (h.globalFormPair V n a a x).re := by
  have hi := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  rw [h.globalFormPair_inFrame V n _ _ x x hi, h.globalFormPair_inFrame V n a a x x hi,
    Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply, Projective.CovectorPair.projectiveTangentCovectorPair_smul_left, Projective.CovectorPair.projectiveTangentCovectorPair_smul_right]
  exact Holomorphic.CutoffCoordinates.complex_weighted_smul_self_re _ _ _

theorem Holomorphic.CutoffCoordinates.smoothComplexFunction_norm_sq_bound
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖f x‖ ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image (hf.continuous.norm.pow 2).continuousOn
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x => (hC ⟨x, Set.mem_univ x, rfl⟩).trans (le_max_left _ _)⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothMul_integral_bound
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n),
      (h.formIntegralPair V n (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a)).re ≤
        C * (h.formIntegralPair V n a a).re := by
  obtain ⟨C, hC, hb⟩ := Holomorphic.CutoffCoordinates.smoothComplexFunction_norm_sq_bound V f hf
  refine ⟨C, hC, fun n a => ?_⟩
  have hp (x : V.analyticSpace) :
      (h.globalFormPair V n (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) x).re ≤
        C * (h.globalFormPair V n a a x).re := by
    rw [h.globalFormPair_smoothMul_self V n f hf a x]
    exact mul_le_mul_of_nonneg_right (hb x) (h.globalFormPair_nonneg V n a x)
  calc
    _ = ∫ x, (h.globalFormPair V n (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) x).re ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      h.formIntegralPair_re V n _ _
    _ ≤ ∫ x, C * (h.globalFormPair V n a a x).re ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V :=
      integral_mono (h.globalFormPair_integrable V n _ _).re ((h.globalFormPair_integrable V n a a).re.const_mul C) hp
    _ = _ := (integral_const_mul C _).trans (congrArg (fun r : ℝ => C * r) (h.formIntegralPair_re V n a a).symm)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_re_chart
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (n : ℕ) (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    (h.globalFormPair V n a b (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re =
      h.weight i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hz.2⟩ *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z)
            (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (b.val i).extension z)).re := by
  have hp := congrArg Complex.re (h.projectiveGlobalPair_inFrame V e he n a b i hz)
  rw [h.projectiveWeightChart_apply V e i hz] at hp
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  exact mul_left_cancel₀ (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz.1).ne' hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
