import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

noncomputable section
open Set Metric Filter
open scoped Topology

namespace OAI.Geometry.Nikodym

/-- The approximate intermediate-point property of a length metric.  The
first distance is exact; the remaining leg loses an arbitrarily small amount. -/
def HasApproximateIntermediatePoints (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (x y : X) (s ε : ℝ), 0 < s → s < dist x y → 0 < ε →
    ∃ z, dist x z = s ∧ dist z y < dist x y - s + ε

/-- A positive distance level in a length metric has uniformly sized holes.
No nearest point or minimizing geodesic is required. -/
theorem HasApproximateIntermediatePoints.distance_level_hole
    {X : Type*} [PseudoMetricSpace X]
    (hX : HasApproximateIntermediatePoints X) {A : Set X} (hA : A.Nonempty)
    {x : X} {δ r : ℝ} (hx : infDist x A = δ)
    (hr : 0 < r) (hsmall : 4 * r < δ) :
    ∃ y : X, dist x y = 4 * r ∧
      ∀ z ∈ closedBall y r, infDist z A < δ := by
  obtain ⟨a, ha, hxa⟩ := (infDist_lt_iff hA).mp
    (show infDist x A < δ + r / 2 by rw [hx]; linarith)
  have hleg : 4 * r < dist x a :=
    hsmall.trans_le (hx ▸ infDist_le_dist_of_mem ha)
  obtain ⟨y, hxy, hya⟩ := hX x a (4*r) (r/2) (by positivity) hleg (by positivity)
  refine ⟨y, hxy, ?_⟩
  intro z hz
  have hzy : dist z y ≤ r := hz
  have hy : infDist y A ≤ dist y a := infDist_le_dist_of_mem ha
  have hz' : infDist z A ≤ infDist y A + dist z y := infDist_le_infDist_add_dist
  linarith

theorem HasApproximateIntermediatePoints.distance_level_disjoint_closedBall
    {X : Type*} [PseudoMetricSpace X]
    (hX : HasApproximateIntermediatePoints X) {A : Set X} (hA : A.Nonempty)
    {x : X} {δ r : ℝ} (hx : infDist x A = δ)
    (hr : 0 < r) (hsmall : 4 * r < δ) :
    ∃ y : X, dist x y = 4 * r ∧
      Disjoint {z | infDist z A = δ} (closedBall y r) := by
  obtain ⟨y, hxy, hy⟩ := hX.distance_level_hole hA hx hr hsmall
  refine ⟨y, hxy, Set.disjoint_left.mpr ?_⟩
  intro z hz hzball
  exact (hy z hzball).ne hz

end OAI.Geometry.Nikodym
