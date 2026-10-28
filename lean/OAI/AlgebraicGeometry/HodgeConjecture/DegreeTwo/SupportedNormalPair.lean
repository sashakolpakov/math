import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

/-! # Supported Normal Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedNormalPair.Constructions

noncomputable section

/-!
# DegreeTwo: genuine normal pairs for a full support described in a chart

This form applies to the inclusion of the zero locus on an algebraic open
into the whole analytic scheme, with the chart contained in that open.
-/

open scoped _root_.Topology

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- A proved chart description of the full support yields an actual
normal pair retaining the same ambient chart. -/
theorem exists_supported_normalPair (f : M → N) (x : M)
    (q : OpenPartialHomeomorph N (E × F))
    (hxq : f x ∈ q.source) (hqx : q (f x) = 0)
    (hq : ∀ y ∈ q.source, y ∈ Set.range f ↔ (q y).2 = 0) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x, P.ambientChart = q := by
  have h0 : (0 : E × F) ∈ q.target := hqx ▸ q.map_source hxq
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (q.open_target.mem_nhds h0)
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ q.target := by
    rw [ball_prod_same]
    exact hball
  refine ⟨{
    radius := r
    radius_pos := hr
    ambientChart := q
    product_subset_target := hprod
    point_mem_source := hxq
    point_coordinates := hqx
    range_iff := ?_ }, rfl⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact hq (q.symm z) (q.map_target (hprod hz))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedNormalPair.Constructions
