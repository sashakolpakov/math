import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformLimit

/-! Classical C² Newtonian solutions for genuinely Hölder, not necessarily differentiable, data. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem newtonianPotential_C2_limit {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 (newtonianPotential f) ∧
      TendstoUniformly (fun k => fderiv ℝ (mollifiedNewtonianPotential f k))
        (fderiv ℝ (newtonianPotential f)) atTop ∧
      TendstoUniformly (fun k => fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k)))
        (fderiv ℝ (fderiv ℝ (newtonianPotential f))) atTop := by
  obtain ⟨r, hr, hrT, hc⟩ := mollifiedNewtonianPotential_cauchy hm f hf hfc hH
    (half_pos hα) (half_lt_self hα) hα1 hh
  obtain ⟨G, hGb, hG⟩ := exists_uniform_limit_of_pairwise_bound
    (fun k => fderiv ℝ (mollifiedNewtonianPotential f k)) r hrT (fun k l x => (hc k l).2.1 x)
  obtain ⟨J, hJb, hJ⟩ := exists_uniform_limit_of_pairwise_bound
    (fun k => fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k))) r hrT (fun k l x => (hc k l).2.2.1 x)
  have hs (k : ℕ) : ContDiff ℝ 2 (mollifiedNewtonianPotential f k) :=
    (contDiff_mollifiedNewtonianPotential (show 1 ≤ m by omega) f hf hfc k).of_le (by simp)
  have hDf (x : EuclideanSpace ℝ (Fin m)) : HasFDerivAt (newtonianPotential f) (G x) x :=
    hasFDerivAt_of_tendstoUniformly hG
      (fun k x => ((hs k).differentiable (by norm_num) x).hasFDerivAt)
      (mollifiedNewtonianPotential_tendsto hm f hf hfc hH hα hh) x
  have hDG (x : EuclideanSpace ℝ (Fin m)) : HasFDerivAt G (J x) x :=
    hasFDerivAt_of_tendstoUniformly hJ
      (fun k x => (((hs k).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt)
      (fun x => hG.tendsto_at x) x
  have hGid : fderiv ℝ (newtonianPotential f) = G := funext (fun x => (hDf x).fderiv)
  have hJid : fderiv ℝ (fderiv ℝ (newtonianPotential f)) = J := by
    rw [hGid]
    exact funext (fun x => (hDG x).fderiv)
  have hJcont : Continuous J := hJ.continuous (Frequently.of_forall (fun k =>
    (((hs k).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous))
  have hGc : ContDiff ℝ 1 G := by
    rw [contDiff_one_iff_fderiv]
    exact ⟨fun x => (hDG x).differentiableAt, by simpa only [funext (fun x => (hDG x).fderiv)] using hJcont⟩
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ (1 + 1) (newtonianPotential f)
    rw [contDiff_succ_iff_fderiv]
    exact ⟨fun x => (hDf x).differentiableAt, by simp, by simpa only [hGid] using hGc⟩
  · simpa only [hGid] using hG
  · simpa only [hJid] using hJ

theorem newtonianPotential_holder_hessian {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), Continuous f → HasCompactSupport f →
      ∀ H, 0 ≤ H → (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x -
        fderiv ℝ (fderiv ℝ (newtonianPotential f)) y‖ ≤ C * H * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, hc⟩ := newtonianPotential_hessian_holder hm hα hα1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  refine ⟨(m : ℝ) * m * C, by positivity, ?_⟩
  intro f hf hfc H hH hh x y
  have hJ := (newtonianPotential_C2_limit hm f hf hfc hH hα hα1 hh).2.2
  have he (i j : Fin m) :
      |(fderiv ℝ (fderiv ℝ (newtonianPotential f)) x - fderiv ℝ (fderiv ℝ (newtonianPotential f)) y)
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤ C * H * ‖x - y‖ ^ α := by
    have ht (z : EuclideanSpace ℝ (Fin m)) :
        Tendsto (fun k => fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k)) z
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) atTop
          (𝓝 (fderiv ℝ (fderiv ℝ (newtonianPotential f)) z
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))) :=
      clm_apply_tendsto (clm_apply_tendsto (hJ.tendsto_at z) (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)
    change |fderiv ℝ (fderiv ℝ (newtonianPotential f)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      fderiv ℝ (fderiv ℝ (newtonianPotential f)) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ _
    apply le_of_tendsto ((ht x).sub (ht y)).abs
    filter_upwards with k
    have hentry := euclidean_bilinear_entry_le_norm
      (fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k)) x -
        fderiv ℝ (fderiv ℝ (mollifiedNewtonianPotential f k)) y) i j
    exact hentry.trans (hc (smoothData (standardMollifier m k) f)
      ((contDiff_smoothData _ f hf).of_le (by simp)) (hasCompactSupport_smoothData _ f hfc)
      H hH (smoothData_holder _ f hf hh) y x)
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m,
        |(fderiv ℝ (fderiv ℝ (newtonianPotential f)) x - fderiv ℝ (fderiv ℝ (newtonianPotential f)) y)
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| := euclidean_bilinear_norm_le_sum _
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, C * H * ‖x - y‖ ^ α :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => he i j))
    _ = _ := by simp; ring

end OAI.Analysis.PDE.Schauder
