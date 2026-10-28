import OAI.Analysis.HodgeTheory.Decomposition.LocalRellich

/-! # Rellich Cover -/

namespace OAI.Analysis.HodgeTheory.Decomposition.RellichCover.Constructions

noncomputable section

/-! A finite genuine manifold chart cover on which the proved local Rellich
compactness theorem applies to every compactly supported family. -/

open Set _root_.Metric

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem exists_projective_rellich_neighborhood (x : V.analyticSpace) :
    ∃ U : Set V.analyticSpace, IsOpen U ∧ x ∈ U ∧ U ⊆ (chartAt V.analyticModel x).source ∧
      ∀ K : Set V.analyticSpace, IsCompact K → K ⊆ U →
        ∀ R : ℝ, 0 ≤ R → IsCompact (closure ((Form.Constructions.smoothToProjectiveL2 V (n + 1)) ''
          {a | (∀ y, y ∉ K → a y = 0) ∧ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ R})) := by
  let e := chartAt V.analyticModel x
  let z := MeasureVolume.Constructions.chartCoordinateForward V e x
  have hx : x ∈ e.source := mem_chart_source _ _
  have hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx
  obtain ⟨r, hr, _, hcompact⟩ := LocalRellich.Constructions.projectiveManifold_local_rellich V e (chart_mem_atlas _ _) n z hz
  let U := e.source ∩ MeasureVolume.Constructions.chartCoordinateForward V e ⁻¹' ball z r
  have hU : IsOpen U := ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn
    e.continuousOn).isOpen_inter_preimage e.open_source isOpen_ball
  refine ⟨U, hU, ⟨hx, mem_ball_self hr⟩, inter_subset_left, fun K hK hKU R hR => ?_⟩
  apply hcompact K hK (hKU.trans inter_subset_left) _ R hR
  rintro _ ⟨y, hy, rfl⟩
  exact ball_subset_closedBall (hKU hy).2

theorem exists_projective_finite_rellich_cover :
    ∃ s : Finset V.analyticSpace, ∃ U : s → Set V.analyticSpace,
      (∀ i, IsOpen (U i)) ∧ (∀ x, ∃ i, x ∈ U i) ∧
      (∀ i, U i ⊆ (chartAt V.analyticModel i.val).source) ∧
      (∀ i, ∀ K : Set V.analyticSpace, IsCompact K → K ⊆ U i →
        ∀ R : ℝ, 0 ≤ R → IsCompact (closure ((Form.Constructions.smoothToProjectiveL2 V (n + 1)) ''
          {a | (∀ y, y ∉ K → a y = 0) ∧ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ R}))) := by
  classical
  choose U hU hxU hUs hcompact using exists_projective_rellich_neighborhood V n
  obtain ⟨s, hcover⟩ := isCompact_univ.elim_finite_subcover U hU (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨s, fun i => U i.val, fun i => hU i.val, ?_, fun i => hUs i.val, fun i => hcompact i.val⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  exact ⟨⟨y, hy⟩, hxy⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.RellichCover.Constructions
