import OAI.Geometry.Nikodym.DistanceHoles

noncomputable section
open Set Metric Filter
open scoped Topology

namespace OAI.Geometry.Nikodym

/-- Local coordinate porosity for the ambient metric's distance levels.
The approximate path lives in the ambient space, and its initial point stays
in the coordinate patch because its distance from the center is exact. -/
theorem local_coordinate_distance_level_hole
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (hX : HasApproximateIntermediatePoints X)
    {A V : Set X} (hA : A.Nonempty) (e : X → Y)
    {K L : ℝ} (hL : 0 < L)
    (he : ∀ u ∈ V, ∀ v ∈ V, dist (e u) (e v) ≤ K * dist u v)
    (hi : ∀ u ∈ V, ∀ v ∈ V, dist u v ≤ L * dist (e u) (e v))
    {x : X} {δ ρ r : ℝ} (hx : infDist x A = δ)
    (hpatch : closedBall x ρ ⊆ V) (hρ : 0 ≤ ρ)
    (hr : 0 < r) (hsmall : 4 * (L * r) < δ)
    (hinside : 4 * (L * r) ≤ ρ) :
    ∃ y : Y, dist (e x) y ≤ (4 * K * L) * r ∧
      Disjoint (e '' ({z | infDist z A = δ} ∩ V)) (closedBall y r) := by
  obtain ⟨y, hxy, hy⟩ := hX.distance_level_hole hA hx (mul_pos hL hr) hsmall
  have hxV : x ∈ V := hpatch (mem_closedBall_self hρ)
  have hyV : y ∈ V := hpatch (by
    change dist y x ≤ ρ
    rw [dist_comm, hxy]
    exact hinside)
  have hexy : dist (e x) (e y) ≤ (4 * K * L) * r := by
    calc
      dist (e x) (e y) ≤ K * dist x y := he x hxV y hyV
      _ = (4 * K * L) * r := by rw [hxy]; ring
  refine ⟨e y, hexy, Set.disjoint_left.mpr ?_⟩
  rintro z ⟨w, ⟨hw, hwV⟩, rfl⟩ hwball
  have hwy : dist w y ≤ L * r :=
    (hi w hwV y hyV).trans (mul_le_mul_of_nonneg_left hwball hL.le)
  exact (hy w hwy).ne hw

theorem local_coordinate_distance_level_small_holes
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (hX : HasApproximateIntermediatePoints X)
    {A V : Set X} (hA : A.Nonempty) (e : X → Y)
    {K L : ℝ} (hL : 0 < L)
    (he : ∀ u ∈ V, ∀ v ∈ V, dist (e u) (e v) ≤ K * dist u v)
    (hi : ∀ u ∈ V, ∀ v ∈ V, dist u v ≤ L * dist (e u) (e v))
    {x : X} {δ : ℝ} (hx : infDist x A = δ) (hδ : 0 < δ)
    (hV : V ∈ 𝓝 x) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∃ y : Y, dist (e x) y ≤ (4 * K * L) * r ∧
        Disjoint (e '' ({z | infDist z A = δ} ∩ V)) (closedBall y r) := by
  obtain ⟨ρ, hρ, hpatch⟩ := Metric.mem_nhds_iff.mp hV
  have hpatch' : closedBall x (ρ/2) ⊆ V := by
    intro y hy
    apply hpatch
    change dist y x < ρ
    change dist y x ≤ ρ/2 at hy
    exact lt_of_le_of_lt hy (by linarith)
  have ht : Tendsto (fun r : ℝ => 4 * (L * r)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => 4 * (L * r)) := by fun_prop
    simpa only [mul_zero] using (hc.continuousAt.mono_left nhdsWithin_le_nhds :
      Tendsto (fun r : ℝ => 4 * (L * r)) (𝓝[>] 0) (𝓝 (4 * (L * 0))))
  filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hδ),
    ht.eventually (gt_mem_nhds (show 0 < ρ/2 by positivity))] with r hr hs hi'
  exact local_coordinate_distance_level_hole hX hA e hL he hi hx hpatch'
    (by positivity) hr hs hi'.le

end OAI.Geometry.Nikodym
