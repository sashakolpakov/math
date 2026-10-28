import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SmallCoefficients

/-! The compact full-space perturbation estimate requires no sign or
symmetry assumption on the small coefficient error. -/

noncomputable section
open Set Metric Laplacian
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

theorem fullspace_hessian_bound_of_support {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) {R α H : ℝ} (hR : 0 ≤ R)
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hs : tsupport u ⊆ closedBall 0 R)
    (hh : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α)
    (x : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H*(2*R+1)^α := by
  have hzero (y : EuclideanSpace ℝ (Fin m)) (hy : R < ‖y‖) : fderiv ℝ (fderiv ℝ u) y = 0 := by
    apply hessian_zero_outside_support u y
    intro ht
    have hz : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hs ht
    linarith
  by_cases hnx : ‖x‖ ≤ R
  · let z : EuclideanSpace ℝ (Fin m) := (R+1) • EuclideanSpace.single k 1
    have hnz : ‖z‖ = R+1 := by simp [z, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R+1)]
    have hHz : fderiv ℝ (fderiv ℝ u) z = 0 := hzero z (by rw [hnz]; linarith)
    have hdist : ‖x-z‖ ≤ 2*R+1 := (norm_sub_le x z).trans (by rw [hnz]; linarith)
    have hb := hh x z
    rw [hHz, sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdist hα) hH)
  · rw [hzero x (lt_of_not_ge hnx), norm_zero]
    positivity

theorem fullspace_small_coefficients {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 3 u)
    (B : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    {R α C θ M F : ℝ} (hR : 0 ≤ R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hs : tsupport u ⊆ closedBall 0 R)
    (hclose : ∀ x, ‖B x‖ ≤ θ)
    (hB : ∀ x y, ‖B x-B y‖ ≤ M*‖x-y‖^α)
    (hLu : ∀ x y,
      |nondivergenceOperator (fun z => 1-B z) u x - nondivergenceOperator (fun z => 1-B z) u y| ≤ F*‖x-y‖^α)
    (hPoisson : ∀ K, 0 ≤ K →
      (∀ x y, |laplacian u x-laplacian u y| ≤ K*‖x-y‖^α) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ C*K*‖x-y‖^α)
    (hsmall : C*(m:ℝ)*m*(θ+M*(2*R+1)^α) ≤ 1/2) :
    ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ 2*C*F*‖x-y‖^α := by
  have huc : HasCompactSupport u := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) R).of_isClosed_subset
    (isClosed_tsupport u) hs
  have hHc := (huc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  have hHC1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  obtain ⟨H₀, hH₀, _, hinit⟩ := compact_C1_holder _ hHC1 hHc hα hα1
  have hfinal := geometric_holder_absorption (fderiv ℝ (fderiv ℝ u)) univ α (C*F) H₀
    (mul_nonneg hC hF) hH₀.le (fun x _ y _ => hinit x y)
  have hstep : ∀ H, 0 ≤ H →
      (∀ x ∈ (univ : Set (EuclideanSpace ℝ (Fin m))), ∀ y ∈ univ,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) →
      ∀ x ∈ univ, ∀ y ∈ univ,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ (C*F+H/2)*‖x-y‖^α := by
    intro H hH hh
    have hsup := fullspace_hessian_bound_of_support k u hR hα hH hs (fun x y => hh x trivial y trivial)
    have hforce := laplacian_perturbation_holder_on B u univ hθ hM hH
      (mul_nonneg hH (Real.rpow_nonneg (by linarith) _))
      (fun x _ => hclose x) (fun x _ y _ => hB x y) (fun x _ => hsup x) hh (fun x _ y _ => hLu x y)
    have hest := hPoisson (F+(m:ℝ)*m*(θ*H+M*(H*(2*R+1)^α))) (by positivity)
      (fun x y => hforce x trivial y trivial)
    intro x _ y _
    apply (hest x y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    have hsmallH := mul_le_mul_of_nonneg_right hsmall hH
    nlinarith only [hsmallH]
  intro x y
  simpa only [mul_assoc] using hfinal hstep x trivial y trivial

end OAI.Analysis.PDE.Schauder
