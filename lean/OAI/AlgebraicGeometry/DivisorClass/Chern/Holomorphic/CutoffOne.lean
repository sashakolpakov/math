import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffCoordinates

/-! # Cutoff One -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The original cutoff differential and codifferential vanish outside the cutoff support. -/

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

theorem Holomorphic.CutoffOne.projectiveGlobalScalar_zero_near {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (hfz : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∉ tsupport f) :
    (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) =ᶠ[𝓝 z] (fun _ => 0) :=
  (notMem_tsupport_iff_eventuallyEq.mp hfz).comp_tendsto
    ((Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_continuousOn V e).continuousAt ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_zero_of_covector (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hb : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (b.val i).extension z = 0) :
    h.globalFormPair V n a b (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 0 := by
  have hp := h.projectiveGlobalPair_inFrame V e he n a b i hz
  rw [hb] at hp
  simp only [Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, _root_.map_zero, inner_zero_right, mul_zero] at hp
  have hρ : (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) ≠ 0 := by
    exact_mod_cast (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz.1).ne'
  exact (mul_eq_zero.mp hp).resolve_left hρ

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_covector_zero (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hfz : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∉ tsupport f) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val.val i).extension z = 0 ∧
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val).val i).extension z = 0 := by
  have hg := Holomorphic.CutoffOne.projectiveGlobalScalar_zero_near V e f hz.1 hfz
  have hdf : fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z = 0 :=
    hg.fderiv_eq.trans (hasFDerivAt_const (0 : ℂ) z).fderiv
  have hgz : f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 0 := hg.eq_of_nhds
  constructor
  · exact (h.cutoffDolbeault_covector V e he i f hf a hz).trans
      (Line.Cutoff.cutoff_symbol_zero_of_scalar_zero
        (fun ℓ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ => Line.Cutoff.lineDolbeaultCutoffSymbol 1 ℓ
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z))
        (Line.Cutoff.lineDolbeaultCutoffSymbol_zero 1 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z)) hdf hgz
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val.val i).extension z))
  · exact (h.cutoffCodifferential_covector V e he i f hf a hz).trans
      (Line.Cutoff.cutoff_symbol_zero_of_scalar_zero
        (fun ℓ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ => Line.Cutoff.lineCodifferentialCutoffSymbol
          (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) ℓ
            (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z))
        (Line.Cutoff.lineCodifferentialCutoffSymbol_zero _ 0 _ _) hdf hgz
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension z))

omit e he i in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_pair_zero (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (x : V.analyticSpace) (hx : x ∉ tsupport f) :
    let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
    h.globalFormPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 A).val x = 0 ∧
      h.globalFormPair V 0 (h.degreeCodifferential V 0 A.val) (h.degreeCodifferential V 0 A.val) x = 0 := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas V.analyticModel x
  let z := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x
  have heq : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z = x := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (mem_chart_source V.analyticModel x)
  have hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x) := by
    refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (mem_chart_source V.analyticModel x), ?_⟩
    change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u x
    rw [heq]
    exact (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  have hnot : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∉ tsupport f := heq ▸ hx
  have hzero := h.cutoff_operators_covector_zero V e he x f hf a hz hnot
  have hD := h.globalFormPair_zero_of_covector V e he x 2
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val _ hz hzero.1
  have hS := h.globalFormPair_zero_of_covector V e he x 0
    (h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val) _ hz hzero.2
  rw [heq] at hD hS
  exact ⟨hD, hS⟩

end

/-! The original Dolbeault operator and codifferential are unchanged where an actual cutoff is locally equal to one. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Holomorphic.CutoffOne.cutoff_symbol_one_of_scalar_one {L F : Type} [Zero L] [AddCommMonoid F] [Module ℂ F]
    (σ : L → F) (hσ : σ 0 = 0) {ℓ : L} {s : ℂ} (hℓ : ℓ = 0) (hs : s = 1) (a : F) :
    σ ℓ + s • a = a := by
  rw [hℓ, hs, hσ, one_smul, zero_add]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_operators_covector_one (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hone : (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) =ᶠ[𝓝 z] (fun _ => (1 : ℂ))) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).val.val i).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val.val i).extension z ∧
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val).val i).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension z := by
  have hdf : fderiv ℝ (fun y => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e y)) z = 0 :=
    hone.fderiv_eq.trans (hasFDerivAt_const (1 : ℂ) z).fderiv
  have hgz : f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 1 := hone.eq_of_nhds
  constructor
  · exact (h.cutoffDolbeault_covector V e he i f hf a hz).trans
      (Holomorphic.CutoffOne.cutoff_symbol_one_of_scalar_one
        (fun ℓ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ => Line.Cutoff.lineDolbeaultCutoffSymbol 1 ℓ
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z))
        (Line.Cutoff.lineDolbeaultCutoffSymbol_zero 1 (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z)) hdf hgz
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val.val i).extension z))
  · exact (h.cutoffCodifferential_covector V e he i f hf a hz).trans
      (Holomorphic.CutoffOne.cutoff_symbol_one_of_scalar_one
        (fun ℓ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ => Line.Cutoff.lineCodifferentialCutoffSymbol
          (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) ℓ
            (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z))
        (Line.Cutoff.lineCodifferentialCutoffSymbol_zero _ 0 _ _) hdf hgz
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension z))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
