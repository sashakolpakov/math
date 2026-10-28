import OAI.Analysis.PDE.Elliptic.DyadicBoxes

open Set BoxIntegral Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*}

theorem exists_dyadicBox_mem_length (B : Box ι) {x : ι → ℝ} (hx : x ∈ B) (n : ℕ) :
    ∃ w : List (Set ι), w.length = n ∧ x ∈ dyadicBox B w := by
  induction n generalizing B with
  | zero => exact ⟨[], rfl, hx⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := Box.exists_mem_splitCenterBox.mpr hx
    obtain ⟨w, hw, hxw⟩ := ih (B.splitCenterBox s) hs
    exact ⟨s :: w, by simp [hw], hxw⟩

theorem dyadicBox_distortion [Fintype ι] (B : Box ι) (w : List (Set ι)) :
    (dyadicBox B w).distortion = B.distortion :=
  Box.distortion_eq_of_sub_eq_div (dyadicBox_width B w)

theorem dyadicBox_dist_le [Fintype ι] (B : Box ι) (w : List (Set ι)) (i : ι)
    {x y : ι → ℝ} (hx : x ∈ dyadicBox B w) (hy : y ∈ dyadicBox B w) :
    dist x y ≤ (B.distortion : ℝ) * ((B.upper i - B.lower i) / 2 ^ w.length) := by
  calc
    dist x y ≤ dist (dyadicBox B w).lower (dyadicBox B w).upper :=
      Real.dist_le_of_mem_pi_Icc (Box.coe_subset_Icc hx) (Box.coe_subset_Icc hy)
    _ ≤ (dyadicBox B w).distortion *
        ((dyadicBox B w).upper i - (dyadicBox B w).lower i) :=
      (dyadicBox B w).dist_le_distortion_mul i
    _ = _ := by rw [dyadicBox_distortion, dyadicBox_width]

/-- Dyadic descendants containing a point eventually fit in every
open neighborhood of that point. No differentiation theorem is needed
when the sets to be covered are open superlevel sets. -/
theorem exists_dyadicBox_subset_open [Fintype ι] [Nonempty ι]
    (B : Box ι) {U : Set (ι → ℝ)} (hU : IsOpen U) {x : ι → ℝ}
    (hx : x ∈ B) (hxU : x ∈ U) :
    ∃ w : List (Set ι), x ∈ dyadicBox B w ∧ (dyadicBox B w : Set (ι → ℝ)) ⊆ U := by
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨i⟩ := ‹Nonempty ι›
  have ht : Tendsto (fun n : ℕ ↦ (B.distortion : ℝ) * ((B.upper i - B.lower i) / 2 ^ n))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds heps)).exists
  obtain ⟨w, hw, hxw⟩ := exists_dyadicBox_mem_length B hx n
  refine ⟨w, hxw, ?_⟩
  intro y hy
  apply hball
  rw [Metric.mem_ball]
  have hd := dyadicBox_dist_le B w i hy hxw
  rw [hw] at hd
  exact hd.trans_lt hn

end OAI.Analysis.PDE.Elliptic
