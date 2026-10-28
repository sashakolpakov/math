import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonHolder

/-! Global C²,α bounds with a fixed compact support for the datum. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem newtonianPotential_holder_bounds {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R : ℝ) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), Continuous f → HasCompactSupport f →
      Function.support f ⊆ ball 0 R → ∀ N, 0 ≤ N →
      (∀ x, |f x| ≤ N) → (∀ x y, |f x - f y| ≤ N * ‖x - y‖ ^ α) →
      (∀ x, |newtonianPotential f x| ≤ C * N) ∧
      (∀ x, ‖fderiv ℝ (newtonianPotential f) x‖ ≤ C * N) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x‖ ≤ C * N) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x -
        fderiv ℝ (fderiv ℝ (newtonianPotential f)) y‖ ≤ C * N * ‖x - y‖ ^ α) := by
  obtain ⟨B, hB, hb⟩ := newtonianPotential_hessian_bound hm hα
  obtain ⟨S, hS, hs⟩ := newtonianPotential_holder_hessian hm hα hα1
  let V := volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) (1 + R))
  let B₀ := rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) 2 + V
  let B₂ := (m : ℝ) * m * B * (3 + 2 * V)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hB₀ : 0 ≤ B₀ := add_nonneg (rieszBallMass_nonneg volume 2) hV
  have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
  refine ⟨3 * B₀ + 2 * B₂ + S + 1, by positivity, ?_⟩
  intro f hf hfc hsupport N hN hu hh
  have hsupport' : Function.support f ⊆ ball 0 (1 + R) :=
    hsupport.trans (ball_subset_ball (by linarith))
  have hI : (∫ x, |f x|) ≤ V * N := integral_abs_le_of_support_ball f hsupport' hu
  have hzero (x) : |newtonianPotential f x| ≤ B₀ * N := by
    have h := newtonianPotential_bound hm f (hf.integrable_of_hasCompactSupport hfc) hN hu hI x
    dsimp only [B₀]
    nlinarith
  have hreg := newtonianPotential_C2_limit hm f hf hfc hN hα hα1 hh
  have htwo (x) : ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x‖ ≤ B₂ * N := by
    have hentry (i j : Fin m) :
        |fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤
          B * (3 + 2 * V) * N := by
      have ht := clm_apply_tendsto (clm_apply_tendsto (hreg.2.2.tendsto_at x)
        (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)
      apply le_of_tendsto ht.abs
      filter_upwards with k
      have hrad : (standardMollifier m k).rOut ^ α ≤ 1 :=
        Real.rpow_le_one (le_of_lt (standardMollifier m k).rOut_pos)
          (pow_le_one₀ (by norm_num) (by norm_num)) hα.le
      have hus (z) : |smoothData (standardMollifier m k) f z| ≤ 2 * N := by
        have he := smoothData_error (standardMollifier m k) f hf hN hα.le hh z
        have hle := mul_le_mul_of_nonneg_left hrad hN
        have ht := abs_add_le (smoothData (standardMollifier m k) f z - f z) (f z)
        rw [sub_add_cancel] at ht
        linarith [hu z]
      have hss : Function.support (smoothData (standardMollifier m k) f) ⊆ ball 0 (1 + R) := by
        apply (support_smoothData_subset_ball _ f hsupport).trans
        apply ball_subset_ball
        have hk : (standardMollifier m k).rOut ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      have his : (∫ z, |smoothData (standardMollifier m k) f z|) ≤ V * (2 * N) :=
        integral_abs_le_of_support_ball _ hss hus
      have hess := hb (smoothData (standardMollifier m k) f)
        ((contDiff_smoothData _ f hf).of_le (by simp)) (hasCompactSupport_smoothData _ f hfc)
        N (2 * N) (V * (2 * N)) hN (by positivity) (by positivity)
        (smoothData_holder _ f hf hh) hus his x
      exact (euclidean_bilinear_entry_le_norm _ i j).trans (hess.trans (by ring_nf; rfl))
    calc
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, |fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| :=
        euclidean_bilinear_norm_le_sum _
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, B * (3 + 2 * V) * N :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
      _ = B₂ * N := by simp [B₂]; ring
  have hone := gradient_bound_of_function_hessian_bound _ hreg.1
    (mul_nonneg hB₀ hN) (mul_nonneg hB₂ hN) hzero htwo
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact (hzero x).trans (mul_le_mul_of_nonneg_right (by linarith) hN)
  · intro x
    exact (hone x).trans (by nlinarith)
  · intro x
    exact (htwo x).trans (mul_le_mul_of_nonneg_right (by linarith) hN)
  · intro x y
    exact (hs f hf hfc N hN hh x y).trans (by gcongr; linarith)

end OAI.Analysis.PDE.Schauder
