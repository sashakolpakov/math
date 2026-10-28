import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Green

/-! Dominated convergence for smooth Newtonian regularizations. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem tendsto_shiftedNewtonian_integral {m : ℕ} (hm : 2 ≤ m)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun s : ℝ => ∫ y, shiftedRadialPower (1 - (m : ℝ) / 2) s y * g y)
      (𝓝[>] 0) (𝓝 (∫ y, newtonianKernel m y * g y)) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hzero : ∀ᵐ y : EuclideanSpace ℝ (Fin m), y ≠ 0 := by rw [ae_iff]; simp
  have hi : Integrable (fun y => newtonianKernel m y * ‖g y‖) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_newtonianKernel (show 1 ≤ m by omega)).integrable_smul_right_of_hasCompactSupport
        hg.norm hgc.norm
  apply tendsto_integral_filter_of_dominated_convergence (fun y => newtonianKernel m y * ‖g y‖)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (((contDiff_shiftedRadialPower _ hs).continuous).mul hg).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [hzero] with y hy
    have hs' : 0 < s := hs
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hp : 1 - (m : ℝ) / 2 ≤ 0 := by linarith
    have hn : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [shiftedRadialPower, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_nonpos hn (by linarith) hp
  · exact hi
  · filter_upwards [hzero] with y hy
    have hn : ‖y‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hy))
    have ht : ContinuousAt (fun s : ℝ => (s + ‖y‖ ^ 2) ^ (1 - (m : ℝ) / 2)) 0 :=
      (continuousAt_id.add continuousAt_const).rpow_const (Or.inl (by simpa using hn))
    simpa only [shiftedRadialPower, newtonianKernel, radialPower, zero_add] using
      (ht.tendsto.mono_left nhdsWithin_le_nhds).mul_const (g y)

theorem shiftedNewtonian_compensated_bound {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x v w : EuclideanSpace ℝ (Fin m)) {H α s : ℝ} (hH : 0 ≤ H) (hs : 0 ≤ s)
    (hf : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) {y : EuclideanSpace ℝ (Fin m)} (hy : y ≠ 0) :
    ‖(f (x - y) - f x) * shiftedRadialHessian (1 - (m : ℝ) / 2) s y v w‖ ≤
      H * newtonianSizeConstant m * ‖v‖ * ‖w‖ * ‖y‖ ^ (α - (m : ℝ)) := by
  rw [norm_mul, Real.norm_eq_abs (f (x - y) - f x)]
  calc
    _ ≤ (H * ‖y‖ ^ α) * (newtonianSizeConstant m * ‖y‖ ^ (-(m : ℝ)) * ‖v‖ * ‖w‖) :=
      mul_le_mul (hf y) (shiftedNewtonianHessian_bound m hs hy v w) (norm_nonneg _)
        (mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _))
    _ = _ := by
      rw [show α - (m : ℝ) = α + -(m : ℝ) by ring, Real.rpow_add (norm_pos_iff.mpr hy)]
      ring

theorem tendsto_shiftedNewtonian_compensated {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Measurable f)
    (x v w : EuclideanSpace ℝ (Fin m)) {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α)
    (hholder : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) (R : ℝ) :
    Tendsto (fun s : ℝ => ∫ y in ball 0 R,
      (f (x - y) - f x) * shiftedRadialHessian (1 - (m : ℝ) / 2) s y v w)
      (𝓝[>] 0) (𝓝 (∫ y in ball 0 R, compensatedNewtonianEntry f x v w y)) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hd : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by simpa using hm
  have hzero : ∀ᵐ y : EuclideanSpace ℝ (Fin m) ∂volume.restrict (ball 0 R), y ≠ 0 := by
    apply ae_restrict_of_ae
    rw [ae_iff]; simp
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y => H * newtonianSizeConstant m * ‖v‖ * ‖w‖ * ‖y‖ ^ (α - (m : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (((hf.comp (measurable_const.sub measurable_id)).sub measurable_const).mul
      (continuous_shiftedRadialHessian_apply _ hs v w).measurable).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [hzero] with y hy
    exact shiftedNewtonian_compensated_bound f x v w hH (le_of_lt hs) hholder hy
  · simpa only [finrank_euclideanSpace_fin] using
      (integrableOn_riesz_majorant volume hd hα R).const_mul
        (H * newtonianSizeConstant m * ‖v‖ * ‖w‖)
  · filter_upwards [hzero] with y hy
    have ht := (tendsto_shiftedRadialHessian (1 - (m : ℝ) / 2) hy v w).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have he : newtonianSecond m y = radialPowerHessian (1 - (m : ℝ) / 2) y := by
      exact second_fderiv_radialPower _ hy
    simpa only [compensatedNewtonianEntry, finrank_euclideanSpace_fin, he] using
      ht.const_mul (f (x - y) - f x)

end OAI.Analysis.PDE.Schauder
