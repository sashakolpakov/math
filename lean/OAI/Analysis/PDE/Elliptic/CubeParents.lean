import OAI.Analysis.PDE.Elliptic.CubeGeometry

open Set BoxIntegral
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem euclideanBox_mono {B C : Box ι} (h : B ≤ C) : euclideanBox B ⊆ euclideanBox C :=
  fun _ hx ↦ h hx

omit [Fintype ι] [Nonempty ι] in
theorem cubeCenter_mem_euclideanBox (B : Box ι) : cubeCenter B ∈ euclideanBox B := by
  change ∀ i, B.lower i < (B.lower i + B.upper i) / 2 ∧
    (B.lower i + B.upper i) / 2 ≤ B.upper i
  intro i
  constructor <;> linarith [B.lower_lt_upper i]

omit [Fintype ι] in
theorem cube_halfwidth_le_of_le {B C : Box ι} {r R : ℝ} (h : B ≤ C)
    (hB : ∀ i, B.upper i - B.lower i = 2 * r)
    (hC : ∀ i, C.upper i - C.lower i = 2 * R) : r ≤ R := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hlo := (Box.le_iff_bounds.mp h).1 i
  have hhi := (Box.le_iff_bounds.mp h).2 i
  linarith [hB i, hC i]

omit [Fintype ι] [Nonempty ι] in
theorem splitCenterBox_halfwidth (B : Box ι) {r : ℝ}
    (hB : ∀ i, B.upper i - B.lower i = 4 * r) (s : Set ι) (i : ι) :
    (B.splitCenterBox s).upper i - (B.splitCenterBox s).lower i = 2 * r := by
  rw [Box.upper_sub_lower_splitCenterBox, hB]
  ring

/-- Every point of a parent cube lies in a fixed dimensional dilate
of the inscribed ball of any child cube. -/
theorem parent_subset_child_ball (B : Box ι) {r : ℝ} (hr : 0 ≤ r)
    (hB : ∀ i, B.upper i - B.lower i = 4 * r) (s : Set ι) :
    euclideanBox B ⊆ Metric.closedBall (cubeCenter (B.splitCenterBox s))
      (3 * (Fintype.card ι : ℝ) * r) := by
  intro x hx
  have hn : ‖x - cubeCenter (B.splitCenterBox s)‖ ≤
      (Fintype.card ι : ℝ) * (3 * r) := by
    apply norm_euclidean_le_card_mul _ (by positivity)
    intro i
    change |x i - ((B.splitCenterBox s).lower i + (B.splitCenterBox s).upper i) / 2| ≤ 3 * r
    have hxi : B.lower i < x i ∧ x i ≤ B.upper i := hx i
    by_cases hi : i ∈ s
    · simp only [Box.splitCenterBox, Set.piecewise, hi, ite_true]
      rw [abs_le]
      constructor <;> linarith [hB i, hxi.1, hxi.2]
    · simp only [Box.splitCenterBox, Set.piecewise, hi, ite_false]
      rw [abs_le]
      constructor <;> linarith [hB i, hxi.1, hxi.2]
  rw [Metric.mem_closedBall, dist_eq_norm]
  nlinarith

end OAI.Analysis.PDE.Elliptic
