import OAI.Analysis.PDE.Elliptic.Scaling

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem gradient_norm_sq (x : E) : gradient (fun y : E ↦ ‖y‖ ^ 2) x = (2 : ℝ) • x := by
  rw [gradient, (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  change (toDual ℝ E).symm ((2 : ℕ) • (toDual ℝ E) x) = _
  rw [map_nsmul, LinearIsometryEquiv.symm_apply_apply]
  simp only [two_smul]

omit [FiniteDimensional ℝ E] in
theorem norm_sq_sub_contDiff (z : E) : ContDiff ℝ ⊤ (fun y : E ↦ ‖y - z‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

theorem gradient_norm_sq_sub (z x : E) :
    gradient (fun y : E ↦ ‖y - z‖ ^ 2) x = (2 : ℝ) • (x - z) := by
  have hd : Differentiable ℝ (fun y : E ↦ ‖y‖ ^ 2) :=
    (contDiff_norm_sq ℝ : ContDiff ℝ ⊤ (fun y : E ↦ ‖y‖ ^ 2)).differentiable (by simp)
  have h := gradient_rescalePoint hd (-z) 1 x
  simpa only [rescalePoint, one_smul, gradient_norm_sq, sub_eq_add_neg, add_comm] using h

theorem fderiv_gradient_norm_sq_sub (z x : E) :
    fderiv ℝ (gradient (fun y : E ↦ ‖y - z‖ ^ 2)) x =
      (2 : ℝ) • ContinuousLinearMap.id ℝ E := by
  have hg : gradient (fun y : E ↦ ‖y - z‖ ^ 2) = fun y ↦ (2 : ℝ) • (y - z) :=
    funext (gradient_norm_sq_sub z)
  rw [hg]
  exact (((hasFDerivAt_id x).sub_const z).const_smul (2 : ℝ)).fderiv

theorem ellipticTrace_norm_sq_sub (A : E → E →L[ℝ] E) (z x : E) :
    ellipticTrace A (fun y : E ↦ ‖y - z‖ ^ 2) x =
      2 * LinearMap.trace ℝ E (A x).toLinearMap := by
  rw [ellipticTrace, fderiv_gradient_norm_sq_sub]
  have he : (A x).comp ((2 : ℝ) • ContinuousLinearMap.id ℝ E) = (2 : ℝ) • A x := by
    ext v
    simp
  rw [he, ContinuousLinearMap.toLinearMap_smul, map_smul]
  rfl

def quadraticBarrier (z : E) (R : ℝ) (x : E) : ℝ := R ^ 2 - ‖x - z‖ ^ 2

omit [FiniteDimensional ℝ E] in
theorem quadraticBarrier_contDiff (z : E) (R : ℝ) :
    ContDiff ℝ ⊤ (quadraticBarrier z R) := contDiff_const.sub (norm_sq_sub_contDiff z)

theorem ellipticTrace_quadraticBarrier (A : E → E →L[ℝ] E) (z x : E) (R : ℝ) :
    ellipticTrace A (quadraticBarrier z R) x =
      -2 * LinearMap.trace ℝ E (A x).toLinearMap := by
  change ellipticTrace A (fun y ↦ R ^ 2 - ‖y - z‖ ^ 2) x = _
  rw [ellipticTrace_const_sub A ((norm_sq_sub_contDiff z).of_le (by simp)),
    ellipticTrace_norm_sq_sub]
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem quadraticBarrier_nonneg {z x : E} {R : ℝ} (hR : 0 ≤ R)
    (hx : x ∈ Metric.closedBall z R) : 0 ≤ quadraticBarrier z R x := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  dsimp [quadraticBarrier]
  nlinarith [norm_nonneg (x - z)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem quadraticBarrier_le (z x : E) (R : ℝ) : quadraticBarrier z R x ≤ R ^ 2 := by
  dsimp [quadraticBarrier]
  nlinarith [sq_nonneg ‖x - z‖]

theorem trace_ge_of_quadratic_lower (A : E →L[ℝ] E) {lam : ℝ}
    (hA : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A v)) :
    lam * Module.finrank ℝ E ≤ LinearMap.trace ℝ E A.toLinearMap := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    lam * Module.finrank ℝ E = ∑ _i : Fin (Module.finrank ℝ E), lam := by simp [mul_comm]
    _ ≤ ∑ i, inner ℝ (b i) (A (b i)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [b.orthonormal.norm_eq_one i, one_pow, mul_one] using hA (b i)

theorem ellipticTrace_quadratic_correction (A : E → E →L[ℝ] E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (z x : E) (R : ℝ) {lam K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hLu : ellipticTrace A u x ≤ 2 * K * lam * Module.finrank ℝ E) :
    ellipticTrace A (fun y ↦ u y + K • quadraticBarrier z R y) x ≤ 0 := by
  rw [ellipticTrace_add_smul A hu ((quadraticBarrier_contDiff z R).of_le (by simp)),
    ellipticTrace_quadraticBarrier]
  have htr := mul_le_mul_of_nonneg_left (trace_ge_of_quadratic_lower (A x) hA) hK
  nlinarith

end OAI.Analysis.PDE.Elliptic
