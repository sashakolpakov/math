import OAI.Analysis.PDE.Elliptic.Boundary.Pullback

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem second_fderiv_norm_bound {g : E → E} (x v w : E) :
    ‖fderiv ℝ (fderiv ℝ g) x v w‖ ≤ ‖iteratedFDeriv ℝ 2 g x‖ * ‖v‖ * ‖w‖ := by
  have hh := (iteratedFDeriv ℝ 2 g x).le_opNorm ![v, w]
  simpa [iteratedFDeriv_two_apply, Fin.prod_univ_two, mul_assoc] using hh

theorem hessian_linear_comp_norm (L : E →L[ℝ] ℝ) {g : E → E} {x : E}
    (hg : ContDiffAt ℝ 2 g x) :
    ‖fderiv ℝ (gradient (fun y => L (g y))) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ 2 g x‖ := by
  let H := fderiv ℝ (gradient (fun y => L (g y))) x
  have hk : ContDiffAt ℝ 2 (fun y => L (g y)) x := L.contDiff.contDiffAt.comp x hg
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  change ‖H v‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ 2 g x‖ * ‖v‖
  by_cases hz : H v = 0
  · rw [hz, norm_zero]; positivity
  have hp : 0 < ‖H v‖ := norm_pos_iff.mpr hz
  have he : ‖H v‖ ^ 2 = L (fderiv ℝ (fderiv ℝ g) x v (H v)) := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (fderiv ℝ (gradient (fun y => L (g y))) x v) (H v) = _
    rw [inner_fderiv_gradient_at hk, second_fderiv_linear_comp L hg]
  have hb := (L.le_opNorm (fderiv ℝ (fderiv ℝ g) x v (H v))).trans
    (mul_le_mul_of_nonneg_left (second_fderiv_norm_bound x v (H v)) (norm_nonneg L))
  rw [Real.norm_eq_abs, ← he, abs_of_nonneg (sq_nonneg _)] at hb
  nlinarith

theorem abs_trace_le_finrank_norm (T : E →L[ℝ] E) :
    |LinearMap.trace ℝ E T.toLinearMap| ≤ Module.finrank ℝ E * ‖T‖ := by
  classical
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    |∑ i, inner ℝ (b i) (T (b i))| ≤ ∑ i, |inner ℝ (b i) (T (b i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖T‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hh := abs_real_inner_le_norm (b i) (T (b i))
      rw [b.orthonormal.norm_eq_one i, one_mul] at hh
      exact hh.trans (by simpa only [b.orthonormal.norm_eq_one i, mul_one] using T.le_opNorm (b i))
    _ = _ := by simp []

theorem ellipticTrace_linear_comp_bound (A : E → E →L[ℝ] E) (L : E →L[ℝ] ℝ)
    {g : E → E} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    |ellipticTrace A (fun y => L (g y)) x| ≤
      Module.finrank ℝ E * ‖A x‖ * ‖L‖ * ‖iteratedFDeriv ℝ 2 g x‖ := by
  unfold ellipticTrace
  have htrace := abs_trace_le_finrank_norm ((A x).comp (fderiv ℝ (gradient (fun y => L (g y))) x))
  have hnorm := ((A x).opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_left (hessian_linear_comp_norm L hg) (norm_nonneg _))
  have hh := htrace.trans (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _))
  simpa only [mul_assoc] using hh

end OAI.Analysis.PDE.Elliptic
