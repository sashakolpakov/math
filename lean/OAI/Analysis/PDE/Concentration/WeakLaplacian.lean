import Mathlib

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory InnerProductSpace Laplacian Filter
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
theorem continuous_laplacian_of_contDiff_two {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Δ f) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply continuous_finsetSum
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdd : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by norm_num)
  exact (hdd.continuous.clm_apply continuous_const).clm_apply continuous_const

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [FiniteDimensional ℝ E] in
theorem second_directional_eq_hessian {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v x : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v = (fderiv ℝ (fderiv ℝ f) x v) v := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  rw [fderiv_clm_apply (hd.differentiable (by norm_num) x) (differentiableAt_const v)]
  simp

theorem integral_second_directional_test {f η : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hη : ContDiff ℝ 2 η) (hs : HasCompactSupport η) (v : E) :
    (∫ x, f x * fderiv ℝ (fun y => fderiv ℝ η y v) x v) =
      ∫ x, η x * fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hdf : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdη : ContDiff ℝ 1 (fun x => fderiv ℝ η x v) :=
    (hη.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hddf : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x v) :=
    (hdf.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous.clm_apply continuous_const
  have hddη : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ η y v) x v) :=
    (hdη.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous.clm_apply continuous_const
  have hsη := hs.fderiv_apply ℝ v
  have hssη := hsη.fderiv_apply ℝ v
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure E))
    ((hddf.mul hη.continuous).integrable_of_hasCompactSupport hs.mul_left)
    ((hdf.continuous.mul hdη.continuous).integrable_of_hasCompactSupport hsη.mul_left)
    ((hdf.continuous.mul hη.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun x _ => hdf.differentiable (by norm_num) x)
    (fun x _ => hη.differentiable (by norm_num) x)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure E))
    ((hdf.continuous.mul hdη.continuous).integrable_of_hasCompactSupport hsη.mul_left)
    ((hf.continuous.mul hddη).integrable_of_hasCompactSupport hssη.mul_left)
    ((hf.continuous.mul hdη.continuous).integrable_of_hasCompactSupport hsη.mul_left)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hdη.differentiable (by norm_num) x)
  rw [hsecond, hfirst, neg_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _

theorem integral_laplacian_test {f η : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hη : ContDiff ℝ 2 η) (hs : HasCompactSupport η) :
    (∫ x, (Δ η) x * f x) = ∫ x, η x * (Δ f) x := by
  let v := stdOrthonormalBasis ℝ E
  have hformula (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
      Δ g x = ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (v i)) x (v i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis g v]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      second_directional_eq_hessian hg]
  simp_rw [hformula η hη, hformula f hf, Finset.sum_mul, Finset.mul_sum]
  have hL (i) : Integrable (fun x =>
      fderiv ℝ (fun y => fderiv ℝ η y (v i)) x (v i) * f x) := by
    have hd : ContDiff ℝ 1 (fun y => fderiv ℝ η y (v i)) :=
      (hη.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hdd : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ η y (v i)) x (v i)) :=
      (hd.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous.clm_apply continuous_const
    exact (hdd.mul hf.continuous).integrable_of_hasCompactSupport
      ((hs.fderiv_apply ℝ (v i)).fderiv_apply ℝ (v i)).mul_right
  have hR (i) : Integrable (fun x =>
      η x * fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i)) := by
    have hd : ContDiff ℝ 1 (fun y => fderiv ℝ f y (v i)) :=
      (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hdd : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i)) :=
      (hd.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous.clm_apply continuous_const
    exact (hη.continuous.mul hdd).integrable_of_hasCompactSupport hs.mul_right
  rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hR i)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_comm] using integral_second_directional_test hf hη hs (v i)

/-- A classical C² function satisfying the weak Laplacian identity has
the stated pointwise Laplacian. The integration by parts and test-function
uniqueness steps are proved, rather than included as assumptions. -/
theorem laplacian_eq_of_weak_identity {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Continuous g)
    (hweak : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ x, (Δ η) x * f x) = ∫ x, η x * g x) : Δ f = g := by
  have hΔ := continuous_laplacian_of_contDiff_two hf
  apply Measure.eq_of_ae_eq (μ := volume) _ hΔ hg
  apply ae_eq_of_integral_contDiff_smul_eq hΔ.locallyIntegrable hg.locallyIntegrable
  intro η hη hs
  simp only [smul_eq_mul]
  rw [← integral_laplacian_test hf (hη.of_le (by simp)) hs]
  exact hweak η hη hs

theorem nonpos_of_nonpositive_test_integrals {g : E → ℝ} (hg : Continuous g)
    {U : Set E} (hU : IsOpen U)
    (htest : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → (∀ x, 0 ≤ η x) → (∫ x, η x * g x) ≤ 0) :
    ∀ x ∈ U, g x ≤ 0 := by
  intro x hx
  by_contra! hpos
  have hnb : U ∩ {y | 0 < g y} ∈ nhds x :=
    inter_mem (hU.mem_nhds hx) ((isOpen_lt continuous_const hg).mem_nhds hpos)
  obtain ⟨η, hsU, hs, hη, hrange, hxη⟩ := exists_contDiff_tsupport_subset (n := ⊤) hnb
  have hηnonneg (y : E) : 0 ≤ η y := (hrange ⟨y, rfl⟩).1
  have hnonneg (y : E) : 0 ≤ η y * g y := by
    by_cases hy : η y = 0
    · simp [hy]
    · exact mul_nonneg (hηnonneg y) (hsU (subset_tsupport η hy)).2.le
  have hprod : Continuous (fun y => η y * g y) := hη.continuous.mul hg
  have hpositive : 0 < ∫ y, η y * g y :=
    hprod.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) hs.mul_right hnonneg
      (by simpa only [hxη, one_mul] using hpos.ne')
  exact (htest η hη hs (hsU.trans Set.inter_subset_left) hηnonneg).not_gt hpositive

/-- A weak upper Laplacian bound gives the classical upper bound, including
on an open subdomain when tests are required to be supported there. -/
theorem laplacian_le_of_weak_inequality {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {U : Set E} (hU : IsOpen U) {δ : ℝ}
    (hweak : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → (∀ x, 0 ≤ η x) →
      (∫ x, (Δ η) x * f x) ≤ δ * ∫ x, η x) :
    ∀ x ∈ U, Δ f x ≤ δ := by
  have hΔ := continuous_laplacian_of_contDiff_two hf
  have hnonpos : ∀ x ∈ U, Δ f x - δ ≤ 0 :=
    nonpos_of_nonpositive_test_integrals (g := fun x => Δ f x - δ)
      (hΔ.sub continuous_const) hU (by
    intro η hη hs hsU hn
    have hi₁ : Integrable (fun x => η x * Δ f x) :=
      (hη.continuous.mul hΔ).integrable_of_hasCompactSupport hs.mul_right
    have hi₂ : Integrable (fun x => η x * δ) :=
      (hη.continuous.mul continuous_const).integrable_of_hasCompactSupport hs.mul_right
    simp_rw [mul_sub]
    rw [integral_sub hi₁ hi₂, integral_mul_const,
      ← integral_laplacian_test hf (hη.of_le (by simp)) hs]
    linarith [hweak η hη hs hsU hn])
  intro x hx
  exact sub_nonpos.mp (hnonpos x hx)

end OAI.Analysis.PDE.Concentration
