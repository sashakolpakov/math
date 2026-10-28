import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Limits -/

namespace OAI.RepresentationTheory.Weil.Local.Limits.Construction

noncomputable section

/-! L² limit tools for passing the local Plancherel identity to compact indicators. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ENNReal

theorem L2_norm_sq_integral
    {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable f)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, invOf_eq_inv]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖))

theorem L2_toLp_dist_sq
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    {f g : E → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [dist_eq_norm, L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
  simp only [hx, hfx, hgx, Pi.sub_apply]

theorem L2_toLp_norm_sq
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    {f : E → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem L2_toLp_tendsto_of_integral_norm_sq
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    {f : ℕ → E → ℂ} {g : E → ℂ}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hsquare : Tendsto (fun j => dist ((hf j).toLp (f j)) (hg.toLp g) ^ 2) atTop (𝓝 0) := by
    simpa only [L2_toLp_dist_sq] using hlim
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  change Tendsto (fun j => Real.sqrt (dist ((hf j).toLp (f j)) (hg.toLp g) ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at h
  simpa only [Real.sqrt_sq (dist_nonneg), Real.sqrt_zero] using h

theorem cauchySeq_of_dist_eq_mul
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℕ → X} {g : ℕ → Y} (a : ℝ) (ha : 0 < a)
    (hfg : ∀ j l, dist (g j) (g l) = a * dist (f j) (f l))
    (hf : CauchySeq f) : CauchySeq g := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf (ε / a) (div_pos hε ha)
  refine ⟨N, fun j hj l hl => ?_⟩
  rw [hfg]
  simpa only [mul_comm] using (lt_div_iff₀ ha).mp (hN j hj l hl)

theorem L2_limit_eq_of_pointwise
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    {f : ℕ → E → ℂ} {g : E → ℂ} (hf : ∀ j, MemLp (f j) 2 μ)
    {G : Lp ℂ 2 μ} (hG : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 G))
    (hpoint : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    G =ᵐ[μ] g := by
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have hae : ∀ᵐ x ∂μ, ∀ j : ℕ, ((hf j).toLp (f j)) x = f j x :=
    ae_all_iff.mpr (fun j => (hf j).coeFn_toLp)
  filter_upwards [hlim, hae] with x hx hfx
  simp only [hfx] at hx
  exact tendsto_nhds_unique hx ((hpoint x).comp hns.tendsto_atTop)

theorem plancherel_pass_to_limit
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    {f F : ℕ → E → ℂ} {g G : E → ℂ}
    (hf : ∀ j, MemLp (f j) 2 μ) (hF : ∀ j, MemLp (F j) 2 μ) (hg : MemLp g 2 μ)
    (hflim : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hpoint : ∀ x, Tendsto (fun j => F j x) atTop (𝓝 (G x)))
    (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ j, (∫ x, ‖F j x‖ ^ 2 ∂μ) = c * ∫ x, ‖f j x‖ ^ 2 ∂μ)
    (hdiff : ∀ j l, (∫ x, ‖F j x - F l x‖ ^ 2 ∂μ) =
      c * ∫ x, ‖f j x - f l x‖ ^ 2 ∂μ) :
    MemLp G 2 μ ∧ (∫ x, ‖G x‖ ^ 2 ∂μ) = c * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  let u : ℕ → Lp ℂ 2 μ := fun j => (hf j).toLp (f j)
  let v : ℕ → Lp ℂ 2 μ := fun j => (hF j).toLp (F j)
  have hulim : Tendsto u atTop (𝓝 (hg.toLp g)) :=
    L2_toLp_tendsto_of_integral_norm_sq μ hf hg hflim
  have hdist (j l : ℕ) : dist (v j) (v l) = Real.sqrt c * dist (u j) (u l) := by
    apply (sq_eq_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp
    rw [mul_pow, Real.sq_sqrt hc.le]
    change dist ((hF j).toLp (F j)) ((hF l).toLp (F l)) ^ 2 =
      c * dist ((hf j).toLp (f j)) ((hf l).toLp (f l)) ^ 2
    rw [L2_toLp_dist_sq, L2_toLp_dist_sq, hdiff]
  have hvcauchy : CauchySeq v := cauchySeq_of_dist_eq_mul (Real.sqrt c)
    (Real.sqrt_pos.mpr hc) hdist hulim.cauchySeq
  obtain ⟨vlim, hvlim⟩ := cauchySeq_tendsto_of_complete hvcauchy
  have hae : vlim =ᵐ[μ] G := L2_limit_eq_of_pointwise μ hF hvlim hpoint
  have hG : MemLp G 2 μ := (memLp_congr_ae hae).mp (Lp.memLp vlim)
  refine ⟨hG, ?_⟩
  have hnorm' (j : ℕ) : ‖v j‖ ^ 2 = c * ‖u j‖ ^ 2 := by
    change ‖(hF j).toLp (F j)‖ ^ 2 = c * ‖(hf j).toLp (f j)‖ ^ 2
    rw [L2_toLp_norm_sq, L2_toLp_norm_sq, hnorm]
  have hvnorm := hvlim.norm.pow 2
  have hunorm : Tendsto (fun j => ‖v j‖ ^ 2) atTop (𝓝 (c * ‖hg.toLp g‖ ^ 2)) := by
    simp only [hnorm']
    exact tendsto_const_nhds.mul (hulim.norm.pow 2)
  have h := tendsto_nhds_unique hvnorm hunorm
  rw [L2_norm_sq_integral, L2_toLp_norm_sq] at h
  calc
    _ = ∫ x, ‖vlim x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    _ = _ := h

end

end OAI.RepresentationTheory.Weil.Local.Limits.Construction
