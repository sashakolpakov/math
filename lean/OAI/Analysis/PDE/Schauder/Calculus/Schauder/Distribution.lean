import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DeltaMass

/-! The actual distributional Hessian of the Newtonian kernel, with its delta term. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem shiftedRadialHessian_test_split {m : ℕ} (p : ℝ) {s : ℝ} (hs : 0 < s)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (R : ℝ)
    (hsp : Function.support f ⊆ ball 0 R) (v w : EuclideanSpace ℝ (Fin m)) :
    (∫ y, shiftedRadialHessian p s y v w * f y) =
      (∫ y in ball 0 R, (f y - f 0) * shiftedRadialHessian p s y v w) +
        f 0 * ∫ y in ball 0 R, shiftedRadialHessian p s y v w := by
  have hK := continuous_shiftedRadialHessian_apply p hs v w
  have hi1 : IntegrableOn (fun y => (f y - f 0) * shiftedRadialHessian p s y v w) (ball 0 R) :=
    integrableOn_continuous_ball _ ((hf.sub continuous_const).mul hK) R
  have hi2 : IntegrableOn (fun y => f 0 * shiftedRadialHessian p s y v w) (ball 0 R) :=
    integrableOn_continuous_ball _ (continuous_const.mul hK) R
  calc
    _ = ∫ y in ball 0 R, shiftedRadialHessian p s y v w * f y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hz : f y = 0 := by contrapose! hy; exact hsp hy
      simp [hz]
    _ = ∫ y in ball 0 R, (f y - f 0) * shiftedRadialHessian p s y v w +
        f 0 * shiftedRadialHessian p s y v w := by
      congr 1
      funext y
      ring
    _ = _ := by rw [integral_add hi1 hi2, integral_const_mul]

theorem tendsto_shiftedNewtonian_test {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Measurable f)
    (v w : EuclideanSpace ℝ (Fin m)) {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α)
    (hholder : ∀ y, |f y - f 0| ≤ H * ‖y‖ ^ α) (R : ℝ) :
    Tendsto (fun s : ℝ => ∫ y in ball 0 R,
      (f y - f 0) * shiftedRadialHessian (1 - (m : ℝ) / 2) s y v w)
      (𝓝[>] 0) (𝓝 (∫ y in ball 0 R, (f y - f 0) * newtonianEntry m v w y)) := by
  have hh : ∀ y, |(fun z => f (-z)) (0 - y) - (fun z => f (-z)) 0| ≤ H * ‖y‖ ^ α := by
    simpa using hholder
  simpa only [zero_sub, neg_neg, neg_zero, compensatedNewtonianEntry,
    finrank_euclideanSpace_fin, newtonianEntry] using
      tendsto_shiftedNewtonian_compensated hm (fun z => f (-z))
        (hf.comp measurable_neg) 0 v w hH hα hh R

theorem tendsto_shiftedNewtonian_hessian_test {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f)
    {H α R : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hR : 0 < R)
    (hholder : ∀ y, |f y - f 0| ≤ H * ‖y‖ ^ α) (hsp : Function.support f ⊆ ball 0 R)
    (i j : Fin m) :
    Tendsto (fun s : ℝ => ∫ y, shiftedRadialHessian (1 - (m : ℝ) / 2) s y
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) * f y) (𝓝[>] 0)
      (𝓝 ((∫ y in ball 0 R, (f y - f 0) * newtonianEntry m
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y) +
      f 0 * (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0))) := by
  have hT := tendsto_shiftedNewtonian_test hm f hf.measurable
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) hH hα hholder R
  have hM := (tendsto_shiftedNewtonian_mass hm hR i j).const_mul (f 0)
  apply (hT.add hM).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (shiftedRadialHessian_test_split _ hs f hf R hsp _ _).symm

theorem newtonian_distribution_hessian_of_holder {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {H α R : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hR : 0 < R)
    (hholder : ∀ y, |f y - f 0| ≤ H * ‖y‖ ^ α) (hsp : Function.support f ⊆ ball 0 R)
    (i j : Fin m) :
    (∫ y, newtonianKernel m y * fderiv ℝ (fderiv ℝ f) y
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) =
      (∫ y in ball 0 R, (f y - f 0) * newtonianEntry m
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y) +
      f 0 * (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0) := by
  let v : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i (1 : ℝ)
  let w : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single j (1 : ℝ)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hc : Continuous (fun y => fderiv ℝ (fderiv ℝ f) y v w) :=
    ((hDf.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const
  have hcompact : HasCompactSupport (fun y => fderiv ℝ (fderiv ℝ f) y v w) :=
    ((hfc.fderiv ℝ).fderiv_apply ℝ v).comp_left
      (g := fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ => L w) (by simp)
  have hL := tendsto_shiftedNewtonian_integral hm (fun y => fderiv ℝ (fderiv ℝ f) y v w) hc hcompact
  have hR' := tendsto_shiftedNewtonian_hessian_test (show 1 ≤ m by omega) f hf.continuous
    hH hα hR hholder hsp i j
  apply tendsto_nhds_unique hL
  apply hR'.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (shiftedRadialHessian_green _ hs f hf hfc v w).symm

theorem newtonian_distribution_hessian {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {R : ℝ} (hR : 0 < R) (hsp : Function.support f ⊆ ball 0 R) (i j : Fin m) :
    (∫ y, newtonianKernel m y * fderiv ℝ (fderiv ℝ f) y
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) =
      (∫ y in ball 0 R, (f y - f 0) * newtonianEntry m
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y) +
      f 0 * (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by norm_num)
  apply newtonian_distribution_hessian_of_holder hm f hf hfc C.coe_nonneg zero_lt_one hR ?_ hsp i j
  intro y
  simpa [Real.rpow_one, dist_eq_norm] using hC.dist_le_mul y 0

end OAI.Analysis.PDE.Schauder
