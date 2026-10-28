import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

/-! # Equation Normal Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EquationNormalPair.Constructions

noncomputable section

/-!
# DegreeTwo: the exact local normal pair of a regular equation

A chart with the equation as its last coordinate gives a genuine normal
pair for the inclusion of the full zero locus, after shrinking to balls.
-/

open scoped _root_.Topology

variable {N E : Type} [TopologicalSpace N] [NormedAddCommGroup E]

/-- The actual full zero locus has a normal pair whose normal coordinate
is exactly its defining function. -/
theorem exists_equation_normalPair_with_chart (h : N → ℂ) (x : N) (hx : h x = 0)
    (q : OpenPartialHomeomorph N (E × ℂ))
    (hxq : x ∈ q.source) (hqx : q x = 0)
    (hq : ∀ y ∈ q.source, (q y).2 = h y) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ
      (Subtype.val : {y : N // h y = 0} → N) ⟨x, hx⟩,
      P.ambientChart = q ∧ ∀ y : P.neighborhood, P.normalCoordinate y = h y.val := by
  have h0 : (0 : E × ℂ) ∈ q.target := hqx ▸ q.map_source hxq
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (q.open_target.mem_nhds h0)
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : ℂ) r ⊆ q.target := by
    rw [ball_prod_same]
    exact hball
  let P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ
      (Subtype.val : {y : N // h y = 0} → N) ⟨x, hx⟩ := {
    radius := r
    radius_pos := hr
    ambientChart := q
    product_subset_target := hprod
    point_mem_source := hxq
    point_coordinates := hqx
    range_iff := by
      intro y hy
      have hys : y ∈ q.source := by
        obtain ⟨z, hz, rfl⟩ := hy
        exact q.map_target (hprod hz)
      rw [hq y hys]
      constructor
      · rintro ⟨z, rfl⟩
        exact z.property
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩ }
  refine ⟨P, rfl, ?_⟩
  intro y
  exact hq y.val (P.neighborhood_subset_source y.property)

theorem exists_equation_normalPair (h : N → ℂ) (x : N) (hx : h x = 0)
    (q : OpenPartialHomeomorph N (E × ℂ))
    (hxq : x ∈ q.source) (hqx : q x = 0)
    (hq : ∀ y ∈ q.source, (q y).2 = h y) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ
      (Subtype.val : {y : N // h y = 0} → N) ⟨x, hx⟩,
      ∀ y : P.neighborhood, P.normalCoordinate y = h y.val := by
  obtain ⟨P, _, hP⟩ := exists_equation_normalPair_with_chart h x hx q hxq hqx hq
  exact ⟨P, hP⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EquationNormalPair.Constructions
