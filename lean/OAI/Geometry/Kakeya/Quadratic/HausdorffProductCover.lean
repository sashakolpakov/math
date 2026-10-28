import OAI.MeasureTheory.Kakeya.HausdorffCovers

open Set _root_.MeasureTheory Metric Filter
open scoped ENNReal Topology

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The elementary covering property of a bounded Euclidean cube.
The weighted form keeps the sharp exponent explicit. -/
def FinitePowerCover (T : Set Y) (q : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ δ : ℝ≥0∞, 0 < δ → δ ≤ 1 → ∃ N : ℕ, ∃ V : Fin N → Set Y,
    T ⊆ ⋃ i, V i ∧ (∀ i, ediam (V i) ≤ δ) ∧ (N : ℝ≥0∞) * δ ^ q ≤ C

theorem ediam_prod_le {A : Set X} {B : Set Y} {δ : ℝ≥0∞}
    (hA : ediam A ≤ δ) (hB : ediam B ≤ δ) : ediam (A ×ˢ B) ≤ δ := by
  apply Metric.ediam_le
  intro x hx y hy
  rw [Prod.edist_eq]
  exact max_le (edist_le_of_ediam_le hx.1 hy.1 hA) (edist_le_of_ediam_le hx.2 hy.2 hB)

theorem dimH_countable_prod {Z : Set X} (hZ : Z.Countable) (T : Set Y) :
    dimH (Z ×ˢ T) ≤ dimH T := by
  have he : Z ×ˢ T = ⋃ x ∈ Z, (fun y : Y => (x, y)) '' T := by
    ext p
    rcases p with ⟨px, py⟩
    simp only [mem_prod, mem_iUnion, mem_image, Prod.mk.injEq]
    constructor
    · intro hp
      exact ⟨px, hp.1, py, hp.2, rfl, rfl⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨hxy.1 ▸ hx, hxy.2 ▸ hy⟩
  rw [he, dimH_bUnion hZ]
  apply iSup₂_le
  intro x hx
  have hi : Isometry (fun y : Y => (x, y)) := by
    intro a b
    simp [Prod.edist_eq]
  exact (hi.dimH_image T).le

theorem hausdorff_null_small_cover [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 < s) {A : Set X} (hA : Measure.hausdorffMeasure s A = 0)
    {r ε : ℝ≥0∞} (hr : 0 < r) (hε : 0 < ε) :
    ∃ U : ℕ → Set X, A ⊆ ⋃ j, U j ∧ (∀ j, ediam (U j) ≤ r) ∧
      (∑' j, ediam (U j) ^ s) < ε := by
  have hbound : (⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ j, U j)
      (_ : ∀ j, ediam (U j) ≤ r), ∑' j, ⨆ _ : (U j).Nonempty, ediam (U j) ^ s) ≤
      Measure.hausdorffMeasure s A := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hlt := hbound.trans_lt (hA ▸ hε)
  obtain ⟨U, hcov, hd, hc⟩ := (by simpa only [iInf_lt_iff] using hlt)
  exact ⟨U, hcov, hd, by simpa only [OAI.MeasureTheory.Kakeya.nonempty_ediam_rpow hs] using hc⟩

/-- Removing one countable exceptional set permits every scale to use
only positive-diameter sets, with arbitrarily small total s-cost. -/
theorem hausdorff_null_positive_covers [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 < s) {A : Set X} (hA : Measure.hausdorffMeasure s A = 0) :
    ∃ Z : Set X, Z.Countable ∧ ∃ U : ℕ → ℕ → Set X,
      (∀ n, A \ Z ⊆ ⋃ j, U n j) ∧
      (∀ n j, ediam (U n j) ≤ (1/2 : ℝ≥0∞)^n) ∧
      (∀ n j, ediam (U n j) = 0 → U n j = ∅) ∧
      (∀ n, (∑' j, ediam (U n j)^s) ≤ (1/2 : ℝ≥0∞)^n) := by
  classical
  have hp (n : ℕ) : 0 < (1/2 : ℝ≥0∞)^n := pos_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
  choose V hcov hd hc using fun n => hausdorff_null_small_cover hs hA (hp n) (hp n)
  let Z : Set X := ⋃ n, ⋃ j, if ediam (V n j) = 0 then V n j else ∅
  have hZ : Z.Countable := by
    apply Set.countable_iUnion
    intro n
    apply Set.countable_iUnion
    intro j
    by_cases h : ediam (V n j) = 0
    · simpa only [ite_eq_left h] using (ediam_eq_zero_iff.mp h).countable
    · simp [h]
  let U : ℕ → ℕ → Set X := fun n j => if ediam (V n j) = 0 then ∅ else V n j
  refine ⟨Z, hZ, U, ?_, ?_, ?_, ?_⟩
  · intro n x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov n hx.1)
    have hn : ediam (V n j) ≠ 0 := by
      intro hn
      apply hx.2
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨j, by simpa [hn] using hj⟩⟩
    exact mem_iUnion.mpr ⟨j, by simpa [U, hn] using hj⟩
  · intro n j
    by_cases hj : ediam (V n j) = 0
    · simp [U, hj]
    · simpa [U, hj] using hd n j
  · intro n j
    by_cases hj : ediam (V n j) = 0
    · simp [U, hj]
    · simp [U, hj]
  · intro n
    apply le_trans (ENNReal.tsum_le_tsum fun j => ?_) (hc n).le
    by_cases hj : ediam (V n j) = 0
    · simp [U, hj, hs]
    · simp [U, hj]

end OAI.Geometry.Kakeya.Quadratic
