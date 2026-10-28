import OAI.Geometry.Nikodym.DistanceHoles

noncomputable section
open Set Metric Filter
open scoped Topology

namespace OAI.Geometry.Nikodym

/-- A local two-sided metric comparison carries distance-level holes to
coordinate holes.  Only pairs whose coordinates lie in the patch need the
inverse comparison. -/
theorem coordinate_distance_level_hole
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (hX : HasApproximateIntermediatePoints X)
    {A : Set X} (hA : A.Nonempty) (e : X → Y) {U : Set Y}
    {K L : ℝ} (_ : 0 ≤ K) (hL : 0 < L)
    (he : ∀ u v, dist (e u) (e v) ≤ K * dist u v)
    (hi : ∀ u v, e u ∈ U → e v ∈ U → dist u v ≤ L * dist (e u) (e v))
    {x : X} {δ R r : ℝ} (hx : infDist x A = δ)
    (hpatch : closedBall (e x) R ⊆ U)
    (hr : 0 < r) (hsmall : 4 * (L * r) < δ)
    (hinside : (4 * K * L + 1) * r < R) :
    ∃ y : Y, dist (e x) y ≤ (4 * K * L) * r ∧
      Disjoint (e '' {z | infDist z A = δ}) (closedBall y r) := by
  obtain ⟨y, hxy, hy⟩ := hX.distance_level_hole hA hx (mul_pos hL hr) hsmall
  have hexy : dist (e x) (e y) ≤ (4 * K * L) * r := by
    calc
      dist (e x) (e y) ≤ K * dist x y := he x y
      _ = (4 * K * L) * r := by rw [hxy]; ring
  have heyU : e y ∈ U := hpatch (by
    change dist (e y) (e x) ≤ R
    rw [dist_comm]
    nlinarith)
  refine ⟨e y, hexy, Set.disjoint_left.mpr ?_⟩
  rintro z ⟨w, hw, rfl⟩ hwball
  have hewU : e w ∈ U := hpatch (by
    change dist (e w) (e x) ≤ R
    have htri := dist_triangle (e w) (e y) (e x)
    have hwy : dist (e w) (e y) ≤ r := hwball
    rw [dist_comm (e y) (e x)] at htri
    nlinarith)
  have hwy : dist w y ≤ L * r :=
    (hi w y hewU heyU).trans (mul_le_mul_of_nonneg_left hwball hL.le)
  exact (hy w hwy).ne hw

/-- In a coordinate patch, positive distance levels have a hole at every
sufficiently small radius, with one fixed center-distance/radius ratio. -/
theorem coordinate_distance_level_small_holes
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (hX : HasApproximateIntermediatePoints X)
    {A : Set X} (hA : A.Nonempty) (e : X → Y) {U : Set Y}
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (he : ∀ u v, dist (e u) (e v) ≤ K * dist u v)
    (hi : ∀ u v, e u ∈ U → e v ∈ U → dist u v ≤ L * dist (e u) (e v))
    {x : X} {δ R : ℝ} (hx : infDist x A = δ) (hδ : 0 < δ) (hR : 0 < R)
    (hpatch : closedBall (e x) R ⊆ U) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∃ y : Y, dist (e x) y ≤ (4 * K * L) * r ∧
        Disjoint (e '' {z | infDist z A = δ}) (closedBall y r) := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, 4 * (L * r) < δ := by
    have ht : Tendsto (fun r : ℝ => 4 * (L * r)) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun r : ℝ => 4 * (L * r)) := by fun_prop
      simpa only [mul_zero] using (hc.continuousAt.mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => 4 * (L * r)) (𝓝[>] 0) (𝓝 (4 * (L * 0))))
    exact ht.eventually (gt_mem_nhds hδ)
  have hinside : ∀ᶠ r : ℝ in 𝓝[>] 0, (4 * K * L + 1) * r < R := by
    have ht : Tendsto (fun r : ℝ => (4 * K * L + 1) * r) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun r : ℝ => (4 * K * L + 1) * r) := by fun_prop
      simpa only [mul_zero] using (hc.continuousAt.mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => (4 * K * L + 1) * r) (𝓝[>] 0)
          (𝓝 ((4 * K * L + 1) * 0)))
    exact ht.eventually (gt_mem_nhds hR)
  filter_upwards [self_mem_nhdsWithin, hsmall, hinside] with r hr hs hi'
  exact coordinate_distance_level_hole hX hA e hK hL he hi hx hpatch hr hs hi'

end OAI.Geometry.Nikodym
