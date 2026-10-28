import OAI.Analysis.PDE.Elliptic.Evans.CubeOscillation

open Set Metric
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [MetricSpace E] [ProperSpace E]

def ballUpper (w : E → ℝ) (z : E) (r : ℝ) : ℝ := sSup (w '' closedBall z r)

def ballLower (w : E → ℝ) (z : E) (r : ℝ) : ℝ := sInf (w '' closedBall z r)

theorem ballLower_le_le_ballUpper {w : E → ℝ} (hw : Continuous w)
    {z x : E} {r : ℝ} (hx : x ∈ closedBall z r) :
    ballLower w z r ≤ w x ∧ w x ≤ ballUpper w z r := by
  exact ⟨csInf_le ((isCompact_closedBall z r).bddBelow_image hw.continuousOn)
      (mem_image_of_mem w hx),
    le_csSup ((isCompact_closedBall z r).bddAbove_image hw.continuousOn)
      (mem_image_of_mem w hx)⟩

theorem exists_ballUpper {w : E → ℝ} (hw : Continuous w) (z : E) {r : ℝ}
    (hr : 0 ≤ r) : ∃ x ∈ closedBall z r, w x = ballUpper w z r := by
  have hne : (closedBall z r).Nonempty := ⟨z, by simp [hr]⟩
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall z r).exists_isMaxOn hne hw.continuousOn
  refine ⟨x, hx, le_antisymm (ballLower_le_le_ballUpper hw hx).2 ?_⟩
  apply csSup_le (hne.image w)
  rintro a ⟨y, hy, rfl⟩
  exact hmax hy

theorem exists_ballLower {w : E → ℝ} (hw : Continuous w) (z : E) {r : ℝ}
    (hr : 0 ≤ r) : ∃ x ∈ closedBall z r, w x = ballLower w z r := by
  have hne : (closedBall z r).Nonempty := ⟨z, by simp [hr]⟩
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall z r).exists_isMinOn hne hw.continuousOn
  refine ⟨x, hx, le_antisymm ?_ (ballLower_le_le_ballUpper hw hx).1⟩
  apply le_csInf (hne.image w)
  rintro a ⟨y, hy, rfl⟩
  exact hmin hy

theorem ball_extrema_mono {w : E → ℝ} (hw : Continuous w) (z : E) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    ballLower w z s ≤ ballLower w z r ∧ ballUpper w z r ≤ ballUpper w z s := by
  obtain ⟨x, hx, hxw⟩ := exists_ballLower hw z hr
  obtain ⟨y, hy, hyw⟩ := exists_ballUpper hw z hr
  constructor
  · rw [← hxw]
    exact (ballLower_le_le_ballUpper hw (closedBall_subset_closedBall hrs hx)).1
  · rw [← hyw]
    exact (ballLower_le_le_ballUpper hw (closedBall_subset_closedBall hrs hy)).2

def familyOscillation {J : Type*} [Fintype J] (w : J → E → ℝ) (z : E) (r : ℝ) : ℝ :=
  ∑ j, (ballUpper (w j) z r - ballLower (w j) z r)

theorem familyOscillation_nonneg {J : Type*} [Fintype J]
    {w : J → E → ℝ} (hw : ∀ j, Continuous (w j)) (z : E) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ familyOscillation w z r := by
  apply Finset.sum_nonneg
  intro j _
  obtain ⟨hlo, hhi⟩ := ballLower_le_le_ballUpper (hw j) (show z ∈ closedBall z r by simp [hr])
  linarith

theorem familyOscillation_mono {J : Type*} [Fintype J]
    {w : J → E → ℝ} (hw : ∀ j, Continuous (w j)) (z : E) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    familyOscillation w z r ≤ familyOscillation w z s := by
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨hlo, hhi⟩ := ball_extrema_mono (hw j) z hr hrs
  linarith

theorem abs_sub_le_ball_oscillation {w : E → ℝ} (hw : Continuous w)
    {z x y : E} {r : ℝ} (hx : x ∈ closedBall z r) (hy : y ∈ closedBall z r) :
    |w x - w y| ≤ ballUpper w z r - ballLower w z r := by
  obtain ⟨hxl, hxu⟩ := ballLower_le_le_ballUpper hw hx
  obtain ⟨hyl, hyu⟩ := ballLower_le_le_ballUpper hw hy
  rw [abs_le]
  constructor <;> linarith

theorem familyOscillation_le_of_abs_le {J : Type*} [Fintype J]
    {w : J → E → ℝ} (hw : ∀ j, Continuous (w j)) (z : E) {r W : ℝ}
    (hr : 0 ≤ r) (hbound : ∀ j x, x ∈ closedBall z r → |w j x| ≤ W) :
    familyOscillation w z r ≤ 2 * W * Fintype.card J := by
  calc
    _ ≤ ∑ _j : J, 2 * W := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨x, hx, hxw⟩ := exists_ballUpper (hw j) z hr
      obtain ⟨y, hy, hyw⟩ := exists_ballLower (hw j) z hr
      have hxu := (abs_le.mp (hbound j x hx)).2
      have hyl := (abs_le.mp (hbound j y hy)).1
      rw [← hxw, ← hyw]
      linarith
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end OAI.Analysis.PDE.Elliptic
