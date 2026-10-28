import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure

/-! # Compact Metric Cover -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactMetricCover.CM.Construction

noncomputable section

/-! A finite compact chart cover and its measurable disjoint refinement.
The compact pieces keep all coordinate coefficients uniformly bounded. -/

open _root_.MeasureTheory Set
open scoped _root_.Manifold

structure CompactMetricChartCover (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) where
  size : ℕ
  chart : Fin size → OpenPartialHomeomorph V.analyticSpace V.analyticModel
  chart_mem : ∀ i, chart i ∈ atlas V.analyticModel V.analyticSpace
  compactSet : Fin size → Set V.analyticSpace
  isCompact : ∀ i, IsCompact (compactSet i)
  subset_source : ∀ i, compactSet i ⊆ (chart i).source
  covers : ⋃ i, compactSet i = univ

theorem compactMetricChartCover_nonempty (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Nonempty (CompactMetricChartCover V) := by
  classical
  obtain ⟨s, r, K, hcover, hK⟩ := CycleClass.Geometric.CompactChartCover.Cycles.exists_compact_chart_decomposition V.analyticModel
    (isCompact_univ : IsCompact (univ : Set V.analyticSpace))
  let p : Fin (Fintype.card s) → s := (Fintype.equivFin s).symm
  refine ⟨⟨Fintype.card s, (fun i => chartAt V.analyticModel (p i).val),
    (fun i => chart_mem_atlas V.analyticModel _), (fun i => K (p i).val),
    (fun i => (hK _ (p i).property).2.1), ?_, ?_⟩⟩
  · intro i
    exact (hK _ (p i).property).2.2.2.1.trans
      (CycleClass.Geometric.CompactChartCover.Cycles.chartClosedBallDomain_subset_source V.analyticModel _ _)
  · apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ y ∈ s, K y := by rw [← hcover]; trivial
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨Fintype.equivFin s ⟨y, hy⟩, by simpa [p] using hxy⟩

def projectiveCompactMetricCover (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : CompactMetricChartCover V :=
  Classical.choice (compactMetricChartCover_nonempty V)

namespace CompactMetricChartCover

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (C : CompactMetricChartCover V)

def piece (i : Fin C.size) : Set V.analyticSpace := disjointed C.compactSet i

theorem piece_measurable (i : Fin C.size) : MeasurableSet (C.piece i) :=
  MeasureGluing.CM.Construction.disjointed_cover_measurable C.compactSet (fun i => (C.isCompact i).measurableSet) i

theorem piece_subset (i : Fin C.size) : C.piece i ⊆ C.compactSet i :=
  disjointed_subset C.compactSet i

theorem piece_subset_source (i : Fin C.size) : C.piece i ⊆ (C.chart i).source :=
  (C.piece_subset i).trans (C.subset_source i)

theorem pieces_disjoint : Pairwise (fun i j => Disjoint (C.piece i) (C.piece j)) :=
  disjoint_disjointed C.compactSet

theorem pieces_cover : ⋃ i, C.piece i = univ := by
  change ⋃ i, disjointed C.compactSet i = univ
  rw [iUnion_disjointed, C.covers]

theorem exists_piece (x : V.analyticSpace) : ∃ i, x ∈ C.piece i := by
  apply mem_iUnion.mp
  rw [C.pieces_cover]
  trivial

end CompactMetricChartCover

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactMetricCover.CM.Construction
