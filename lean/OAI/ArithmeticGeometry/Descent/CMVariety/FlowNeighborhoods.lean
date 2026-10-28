import OAI.ArithmeticGeometry.Descent.CMVariety.ParametricFlow

/-! # Flow Neighborhoods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FlowNeighborhoods.Abelian

noncomputable section

/-!
Shrink a continuously varying local flow to a common parameter and time
neighborhood lying inside a specified open chart domain. This is derived
from the constructed flow's continuity, not from continuity of the exponential.
-/

open Set _root_.Metric
open scoped _root_.Topology NNReal

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ P] [NormedSpace ℝ V] in
theorem exists_uniform_flow_neighborhood
    (flow : P × ℝ → V) (p₀ : P) (r : ℝ≥0) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε)
    (hflow : ContinuousOn flow (closedBall p₀ r ×ˢ Ioo (-ε) ε))
    (hzero : flow (p₀, 0) = 0)
    (U : Set (P × V)) (hU : IsOpen U) (hcenter : (p₀, 0) ∈ U) :
    ∃ r' : ℝ≥0, 0 < r' ∧ r' ≤ r ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ p ∈ closedBall p₀ r', ∀ t ∈ Ioo (-ε') ε', (p, flow (p, t)) ∈ U := by
  have hrR : (0 : ℝ) < r := hr
  have hdom : closedBall p₀ (r : ℝ) ×ˢ Ioo (-ε) ε ∈ 𝓝 (p₀, (0 : ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds p₀ hrR) (Ioo_mem_nhds (by linarith) hε)
  have hcont : ContinuousAt (fun q : P × ℝ => (q.1, flow q)) (p₀, 0) :=
    continuousAt_fst.prodMk (hflow.continuousAt hdom)
  have hmem : {q : P × ℝ | (q.1, flow q) ∈ U} ∈ 𝓝 (p₀, 0) :=
    hcont.preimage_mem_nhds (hU.mem_nhds (by simpa only [hzero] using hcenter))
  obtain ⟨d, hd, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hd2 : 0 < d / 2 := half_pos hd
  let r' : ℝ≥0 := ⟨min (r : ℝ) (d / 2), le_of_lt (lt_min hrR hd2)⟩
  let ε' := min ε (d / 2)
  have hr' : 0 < r' := lt_min hrR hd2
  have hr'r : r' ≤ r := show (r' : ℝ) ≤ (r : ℝ) from min_le_left _ _
  have hε' : 0 < ε' := lt_min hε hd2
  refine ⟨r', hr', hr'r, ε', hε', min_le_left _ _, ?_⟩
  intro p hp t ht
  apply hsub (a := (p, t))
  change dist (p, t) (p₀, (0 : ℝ)) < d
  rw [Prod.dist_eq]
  apply max_lt
  · have hp' : dist p p₀ ≤ (r' : ℝ) := hp
    exact (hp'.trans (min_le_right _ _)).trans_lt (half_lt_self hd)
  · rw [Real.dist_eq, sub_zero]
    exact ((abs_lt.mpr ht).trans_le (min_le_right _ _)).trans (half_lt_self hd)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FlowNeighborhoods.Abelian
