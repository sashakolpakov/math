import OAI.Analysis.PDE.Green.FluxEstimate

/-! A uniform integral bound for the normal derivative of the boundary cutoff. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

def normalCutoffWeight (r : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * deriv Real.smoothTransition (-((k : ℝ) + 1) * r)

theorem normalCutoffWeight_nonneg (r : ℝ) (k : ℕ) : 0 ≤ normalCutoffWeight r k :=
  mul_nonneg (by positivity) Real.smoothTransition.monotone.deriv_nonneg

theorem continuous_normalCutoffWeight (k : ℕ) : Continuous (fun r => normalCutoffWeight r k) :=
  continuous_const.mul (((Real.smoothTransition.contDiff (n := 1)).continuous_deriv
    (by norm_num)).comp (continuous_const.mul continuous_id))

theorem normalCutoffWeight_mul (r : ℝ) (k : ℕ) :
    normalCutoffWeight r k * r = -transitionSlope (-((k : ℝ) + 1) * r) := by
  unfold normalCutoffWeight transitionSlope
  ring

theorem transitionSlope_nonneg (t : ℝ) : 0 ≤ transitionSlope t := by
  by_cases ht : 0 ≤ t
  · exact mul_nonneg ht Real.smoothTransition.monotone.deriv_nonneg
  · rw [transitionSlope_zero_nonpos (le_of_not_ge ht)]

theorem normalCutoffWeight_mul_norm (r : ℝ) (k : ℕ) :
    normalCutoffWeight r k * ‖r‖ = transitionSlope (-((k : ℝ) + 1) * r) := by
  calc
    _ = ‖normalCutoffWeight r k * r‖ := by
      rw [norm_mul, Real.norm_of_nonneg (normalCutoffWeight_nonneg r k)]
    _ = _ := by
      rw [normalCutoffWeight_mul, norm_neg, Real.norm_of_nonneg (transitionSlope_nonneg _)]

theorem normalCutoffWeight_square_bound {C : ℝ}
    (hC : ∀ t, ‖transitionSlope t‖ ≤ C) (r : ℝ) (k : ℕ) :
    normalCutoffWeight r k * r ^ 2 ≤ C * ‖r‖ := by
  calc
    _ = ‖normalCutoffWeight r k * r‖ * ‖r‖ := by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (normalCutoffWeight_nonneg r k)]
      rw [mul_assoc, ← pow_two, sq_abs]
    _ = ‖transitionSlope (-((k : ℝ) + 1) * r)‖ * ‖r‖ := by
      rw [normalCutoffWeight_mul, norm_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hC _) (norm_nonneg r)

/-- Any smooth transverse field with `Dr(F)+r²≥c>0` controls the total normal
cutoff weight uniformly in the cutoff parameter. The displayed constant is
computed from box-face flux, divergence, and the defining function. -/
theorem normalCutoffWeight_integral_bound {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 1 r)
    {c C : ℝ} (hc : 0 < c) (hC : ∀ t, ‖transitionSlope t‖ ≤ C)
    (hmin : ∀ x ∈ Icc a b, c ≤ (∑ i, fderiv ℝ r x (Pi.single i 1) * F i x) + r x ^ 2)
    (k : ℕ) :
    (∫ x in Icc a b, normalCutoffWeight (r x) k) ≤
      (boxBoundaryNorm a b F + (∫ x in Icc a b,
        ‖∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖) + C * ∫ x in Icc a b, ‖r x‖) / c := by
  let g := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  have hg : Continuous g := continuous_finsetSum _ (fun i _ =>
    (continuous_directional hr (Pi.single i 1)).mul (hF i).continuous)
  have hw : Continuous (fun x => normalCutoffWeight (r x) k) :=
    (continuous_normalCutoffWeight k).comp hr.continuous
  have hwg : Continuous (fun x => normalCutoffWeight (r x) k * g x) := hw.mul hg
  have hwr : Continuous (fun x => normalCutoffWeight (r x) k * r x ^ 2) :=
    hw.mul (hr.continuous.pow 2)
  have hchi : ∀ x, ‖boundaryCutoff (r x) k‖ ≤ 1 := by
    intro x
    rw [boundaryCutoff, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hbnd := integral_normal_derivative_box_bound a b hab F hF
    (contDiff_boundaryCutoff hr k) hchi
  have hnormal (x : Fin (m + 1) → ℝ) :
      (∑ i, fderiv ℝ (fun y => boundaryCutoff (r y) k) x (Pi.single i 1) * F i x) =
        -(normalCutoffWeight (r x) k * g x) := by
    simp_rw [fderiv_boundaryCutoff hr]
    unfold normalCutoffWeight g
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hnormal] at hbnd
  rw [integral_neg, norm_neg] at hbnd
  have hgb : (∫ x in Icc a b, normalCutoffWeight (r x) k * g x) ≤
      boxBoundaryNorm a b F + ∫ x in Icc a b,
        ‖∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖ :=
    (le_abs_self _).trans hbnd
  have hrb : (∫ x in Icc a b, normalCutoffWeight (r x) k * r x ^ 2) ≤
      C * ∫ x in Icc a b, ‖r x‖ := by
    rw [← integral_const_mul]
    apply integral_mono (hw.mul (hr.continuous.pow 2)).integrableOn_Icc
      (continuous_const.mul hr.continuous.norm).integrableOn_Icc
    exact fun x => normalCutoffWeight_square_bound hC (r x) k
  have hmain : (∫ x in Icc a b, c * normalCutoffWeight (r x) k) ≤
      ∫ x in Icc a b,
        normalCutoffWeight (r x) k * g x + normalCutoffWeight (r x) k * r x ^ 2 := by
    apply setIntegral_mono_on (continuous_const.mul hw).integrableOn_Icc
      ((hw.mul hg).add (hw.mul (hr.continuous.pow 2))).integrableOn_Icc measurableSet_Icc
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (hmin x hx) (normalCutoffWeight_nonneg (r x) k)
    change c * normalCutoffWeight (r x) k ≤
      normalCutoffWeight (r x) k * g x + normalCutoffWeight (r x) k * r x ^ 2
    change normalCutoffWeight (r x) k * c ≤ normalCutoffWeight (r x) k * (g x + r x ^ 2) at hh
    nlinarith
  rw [integral_const_mul, integral_add hwg.integrableOn_Icc hwr.integrableOn_Icc] at hmain
  apply (le_div_iff₀ hc).2
  nlinarith

theorem linearForm_nonzero_coordinate {m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ i, L (Pi.single i 1) ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply hL
  ext x
  change L x = 0
  have hx : x = ∑ i : Fin m, (x i) • (Pi.single i 1 : Fin m → ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [hn]

theorem linearForm_sum_square_pos {m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    0 < ∑ i, (L (Pi.single i 1)) ^ 2 := by
  obtain ⟨i, hi⟩ := linearForm_nonzero_coordinate L hL
  exact (sq_pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (L (Pi.single j 1))) (Finset.mem_univ i))

/-- A compact box meeting only regular points of the zero level has a uniform
bound on the total normal cutoff weight. No surface measure theorem is assumed. -/
theorem exists_uniform_normalCutoffWeight_bound {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ Icc a b, r x = 0 → fderiv ℝ r x ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, (∫ x in Icc a b, normalCutoffWeight (r x) k) ≤ M := by
  let F := fun (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) =>
    fderiv ℝ r x (Pi.single i 1)
  have hF (i : Fin (m + 1)) : ContDiff ℝ 1 (F i) :=
    (hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hg : Continuous (fun x => (∑ i, F i x ^ 2) + r x ^ 2) :=
    (continuous_finsetSum _ (fun i _ => (hF i).continuous.pow 2)).add (hr.continuous.pow 2)
  have hpos : ∀ x ∈ Icc a b, 0 < (∑ i, F i x ^ 2) + r x ^ 2 := by
    intro x hx
    have hn : 0 ≤ ∑ i, F i x ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    by_cases hz : r x = 0
    · have hp := linearForm_sum_square_pos (fderiv ℝ r x) (hrne x hx hz)
      dsimp only [F] at *
      nlinarith [sq_nonneg (r x)]
    · nlinarith [sq_pos_of_ne_zero hz]
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_forall_le' hg.continuousOn hpos
  obtain ⟨C, _, hC⟩ := exists_transitionSlope_bound
  let M := (boxBoundaryNorm a b F + (∫ x in Icc a b,
      ‖∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖) + C * ∫ x in Icc a b, ‖r x‖) / c
  refine ⟨max M 0, le_max_right _ _, fun k => ?_⟩
  apply le_trans (normalCutoffWeight_integral_bound a b hab F hF
    (hr.of_le (by norm_num)) hc hC (fun x hx => ?_) k) (le_max_left _ _)
  simpa only [F, pow_two] using hmin x hx

end OAI.Analysis.PDE.Green
