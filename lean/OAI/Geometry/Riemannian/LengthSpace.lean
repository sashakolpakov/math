import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace OAI.Geometry.Riemannian

section Extended

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

include I

/-- Finite Riemannian distance is approximated by actual globally `C¹` paths,
locally constant at both endpoints. -/
theorem exists_near_minimizing_C1_path (x y : M) (hd : edist x y ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ ContMDiff 𝓘(ℝ) I 1 γ ∧
      pathELength I γ 0 1 < edist x y + ε ∧
      γ =ᶠ[𝓝 0] (fun _ => x) ∧ γ =ᶠ[𝓝 1] (fun _ => y) := by
  have hr : riemannianEDist I x y < edist x y + ε := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact ENNReal.lt_add_right hd hε.ne'
  exact exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one

/-- Exact starting distance and arbitrarily small triangle excess, obtained on a
near-minimizing `C¹` path by the intermediate value theorem. -/
theorem exists_intermediate_edist (x y : M) (hd : edist x y ≠ ⊤)
    {s ε : ℝ≥0∞} (hs : s ≤ edist x y) (hε : 0 < ε) :
    ∃ z : M, edist x z = s ∧ edist x z + edist z y < edist x y + ε := by
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ := exists_near_minimizing_C1_path (I := I) x y hd hε
  have hc : Continuous (fun t : ℝ => edist x (γ t)) := continuous_const.edist hγ.continuous
  have hmem : s ∈ Icc (edist x (γ 0)) (edist x (γ 1)) := by
    simpa only [hγ0, hγ1, edist_self, mem_Icc] using
      (show 0 ≤ s ∧ s ≤ edist x y from ⟨bot_le, hs⟩)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc zero_le_one hc.continuousOn hmem
  refine ⟨γ t, heq, ?_⟩
  have hleft : edist x (γ t) ≤ pathELength I γ 0 t := by
    rw [IsRiemannianManifold.out (I := I)]
    exact riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 rfl ht.1
  have hright : edist (γ t) y ≤ pathELength I γ t 1 := by
    rw [IsRiemannianManifold.out (I := I)]
    exact riemannianEDist_le_pathELength hγ.contMDiffOn rfl hγ1 ht.2
  calc
    edist x (γ t) + edist (γ t) y ≤ pathELength I γ 0 t + pathELength I γ t 1 :=
      add_le_add hleft hright
    _ = pathELength I γ 0 1 := pathELength_add ht.1 ht.2
    _ < edist x y + ε := hlen

end Extended

section Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

include I

/-- Real-distance intermediate-point property. In particular, Riemannian distance
has approximate midpoints without any completeness or minimizing-geodesic assumption. -/
theorem exists_intermediate_dist (x y : M) {s ε : ℝ}
    (hs : 0 ≤ s) (hsd : s ≤ dist x y) (hε : 0 < ε) :
    ∃ z : M, dist x z = s ∧ dist z y < dist x y - s + ε := by
  have hse : ENNReal.ofReal s ≤ edist x y := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hsd
  obtain ⟨z, heq, hsum⟩ := exists_intermediate_edist (I := I) x y (edist_ne_top x y) hse
    (ENNReal.ofReal_pos.mpr hε)
  have heq' : dist x z = s := by
    rw [edist_dist] at heq
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg hs).mp heq
  have hsum' : dist x z + dist z y < dist x y + ε := by
    simp only [edist_dist] at hsum
    rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg,
      ← ENNReal.ofReal_add dist_nonneg hε.le] at hsum
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hsum
  refine ⟨z, heq', ?_⟩
  linarith

theorem exists_approximate_midpoint (x y : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : M, dist x z ≤ dist x y / 2 + ε ∧ dist z y < dist x y / 2 + ε := by
  have hn : 0 ≤ dist x y := dist_nonneg
  obtain ⟨z, heq, hzy⟩ := exists_intermediate_dist (I := I) x y
    (s := dist x y / 2) (by positivity) (by linarith) hε
  refine ⟨z, ?_, ?_⟩
  · rw [heq]
    linarith
  · linarith

end Metric
end OAI.Geometry.Riemannian
