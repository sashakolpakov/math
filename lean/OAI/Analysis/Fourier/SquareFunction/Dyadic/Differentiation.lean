import OAI.Analysis.Fourier.SquareFunction.Dyadic.Average
import OAI.Analysis.Fourier.SquareFunction.Dyadic.Boxes

/-! Shrinking dyadic boxes recover continuous functions from their averages. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral Filter
open scoped ENNReal Topology

theorem dyadicBox_edge {ι : Type*} (I : Box ι) (l : List (Set ι)) (i : ι) :
    (dyadicBox I l).upper i - (dyadicBox I l).lower i =
      (I.upper i - I.lower i) * (1 / 2 : ℝ) ^ l.length := by
  induction l generalizing I with
  | nil => simp [dyadicBox]
  | cons s l ih =>
    change (dyadicBox (I.splitCenterBox s) l).upper i -
      (dyadicBox (I.splitCenterBox s) l).lower i = _
    rw [ih, I.upper_sub_lower_splitCenterBox]
    simp only [List.length_cons, pow_succ]
    ring

theorem exists_dyadic_word_containing {ι : Type*} (I : Box ι) {x : ι → ℝ}
    (hx : x ∈ I) (N : ℕ) :
    ∃ l : List (Set ι), l.length = N ∧ x ∈ dyadicBox I l := by
  induction N generalizing I with
  | zero => exact ⟨[], rfl, hx⟩
  | succ N ih =>
    obtain ⟨s, hs⟩ := I.exists_mem_splitCenterBox.mpr hx
    obtain ⟨l, hl, hx⟩ := ih (I.splitCenterBox s) hs
    exact ⟨s :: l, by simp [hl], hx⟩

theorem dist_le_dyadic_mesh {ι : Type*} [Fintype ι] (I : Box ι)
    (l : List (Set ι)) {x y : ι → ℝ} (hx : x ∈ dyadicBox I l) (hy : y ∈ dyadicBox I l) :
    dist x y ≤ dist I.upper I.lower * (1 / 2 : ℝ) ^ l.length := by
  apply (dist_pi_le_iff (mul_nonneg dist_nonneg (pow_nonneg (by norm_num) _))).mpr
  intro i
  have hxi := (dyadicBox I l).mem_def.mp hx i
  have hyi := (dyadicBox I l).mem_def.mp hy i
  have hcoord : dist (x i) (y i) ≤
      (dyadicBox I l).upper i - (dyadicBox I l).lower i := by
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [hxi.1, hxi.2, hyi.1, hyi.2],
      by linarith [hxi.1, hxi.2, hyi.1, hyi.2]⟩
  have hwidth : I.upper i - I.lower i ≤ dist I.upper I.lower := by
    simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr (I.lower_lt_upper i))] using
      dist_le_pi_dist I.upper I.lower i
  exact hcoord.trans (by rw [dyadicBox_edge]; exact mul_le_mul_of_nonneg_right hwidth (by positivity))

/-- At every point of a box, sufficiently fine dyadic descendants fit in any
prescribed neighborhood of that point. -/
theorem exists_dyadic_subbox_in_ball {ι : Type*} [Fintype ι] (I : Box ι)
    {x : ι → ℝ} (hx : x ∈ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (Q : Set (ι → ℝ)), Q ∈ dyadicFamily I N ∧ x ∈ Q ∧ Q ⊆ Metric.ball x ε := by
  have ht : Tendsto (fun N : ℕ => dist I.upper I.lower * (1 / 2 : ℝ) ^ N)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨l, hl, hxl⟩ := exists_dyadic_word_containing I hx N
  refine ⟨N, (dyadicBox I l : Set (ι → ℝ)), dyadicBox_mem_dyadicFamily I l hl.le, hxl, ?_⟩
  intro y hy
  exact (dist_le_dyadic_mesh I l hy hxl).trans_lt (by simpa [hl] using hN)

/-- Lower bounds on a function give the same lower bound on its true average. -/
theorem le_positiveSetMean_of_pointwise {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (Q : Set X) (hQm : MeasurableSet Q)
    (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞)
    {c : ℝ} (hc : ∀ x ∈ Q, c ≤ f x) : ENNReal.ofReal c ≤ positiveSetMean μ f Q := by
  have hmul : ENNReal.ofReal c * μ Q ≤ positiveSetMean μ f Q * μ Q := by
    rw [positiveSetMean_mul_measure μ f Q hQ0 hQtop]
    calc
      _ = ∫⁻ _ in Q, ENNReal.ofReal c ∂μ := (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono' hQm (fun x hx => ENNReal.ofReal_le_ofReal (hc x hx))
  calc
    _ = (ENNReal.ofReal c * μ Q) * (μ Q)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQtop, mul_one]
    _ ≤ (positiveSetMean μ f Q * μ Q) * (μ Q)⁻¹ := mul_le_mul_left hmul _
    _ = _ := by rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQtop, mul_one]

/-- Continuous functions are recovered pointwise from their dyadic averages.
The statement also applies to volume restricted to the root box. -/
theorem continuousAt_le_iSup_dyadic_means {ι : Type*} [Fintype ι]
    (I : Box ι) (μ : Measure (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    {x : ι → ℝ} (hx : x ∈ I) (hf : ContinuousAt f x) (hfx : 0 ≤ f x)
    (hQ0 : ∀ N Q, Q ∈ dyadicFamily I N → μ Q ≠ 0)
    (hQtop : ∀ N Q, Q ∈ dyadicFamily I N → μ Q ≠ ∞) :
    ENNReal.ofReal (f x) ≤ ⨆ N : ℕ, familySup (dyadicFamily I N) (positiveSetMean μ f) x := by
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  have hbfin : b ≠ ∞ := (hb.trans ENNReal.ofReal_lt_top).ne
  have hbf : b.toReal < f x := by
    simpa only [ENNReal.toReal_ofReal hfx] using
      (ENNReal.toReal_lt_toReal hbfin ENNReal.ofReal_ne_top).mpr hb
  have hnb : {y | b.toReal < f y} ∈ 𝓝 x := hf.preimage_mem_nhds (Ioi_mem_nhds hbf)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnb
  obtain ⟨N, Q, hQ, hxQ, hQball⟩ := exists_dyadic_subbox_in_ball I hx hε
  have hm := le_positiveSetMean_of_pointwise μ f Q (dyadicFamily_measurable I N hQ)
    (hQ0 N Q hQ) (hQtop N Q hQ) (fun y hy => (hball (hQball hy)).le)
  rw [ENNReal.ofReal_toReal hbfin] at hm
  exact hm.trans ((le_familySup_of_mem hQ hxQ).trans (le_iSup
    (fun N : ℕ => familySup (dyadicFamily I N) (positiveSetMean μ f) x) N))

end OAI.Analysis.Fourier.SquareFunction
