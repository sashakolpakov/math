import OAI.Analysis.PDE.Elliptic.TraceCoercivity

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem differentiable_gradient {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (gradient f) :=
  (toDual ℝ E).symm.differentiable.comp
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))

theorem gradient_const_sub {f : E → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x : E) :
    gradient (fun y ↦ c - f y) x = -gradient f x := by
  simp only [gradient, ((hf x).hasFDerivAt.const_sub c).fderiv, map_neg]

theorem ellipticTrace_const_sub (A : E → E →L[ℝ] E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    ellipticTrace A (fun y ↦ c - f y) x = -ellipticTrace A f x := by
  have hg : gradient (fun y ↦ c - f y) = fun y ↦ -gradient f y :=
    funext (gradient_const_sub (hf.differentiable (by norm_num)) c)
  have hD : fderiv ℝ (gradient (fun y ↦ c - f y)) x = -fderiv ℝ (gradient f) x := by
    rw [hg]
    exact ((differentiable_gradient hf x).hasFDerivAt.neg).fderiv
  unfold ellipticTrace
  rw [hD, ContinuousLinearMap.comp_neg, ContinuousLinearMap.toLinearMap_neg, map_neg]

theorem gradient_add_smul {f g : E → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (c : ℝ) (x : E) :
    gradient (fun y ↦ f y + c • g y) x = gradient f x + c • gradient g x := by
  have hD : fderiv ℝ (fun y ↦ f y + c • g y) x =
      fderiv ℝ f x + c • fderiv ℝ g x :=
    ((hf x).hasFDerivAt.add ((hg x).hasFDerivAt.const_smul c)).fderiv
  simp only [gradient, hD, map_add, map_smul]

theorem ellipticTrace_add_smul (A : E → E →L[ℝ] E) {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (c : ℝ) (x : E) :
    ellipticTrace A (fun y ↦ f y + c • g y) x =
      ellipticTrace A f x + c * ellipticTrace A g x := by
  have hgrad : gradient (fun y ↦ f y + c • g y) =
      fun y ↦ gradient f y + c • gradient g y :=
    funext (gradient_add_smul (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) c)
  have hD : fderiv ℝ (gradient (fun y ↦ f y + c • g y)) x =
      fderiv ℝ (gradient f) x + c • fderiv ℝ (gradient g) x := by
    rw [hgrad]
    exact ((differentiable_gradient hf x).hasFDerivAt.add
      ((differentiable_gradient hg x).hasFDerivAt.const_smul c)).fderiv
  unfold ellipticTrace
  rw [hD, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    map_add, map_smul]
  rfl

theorem trace_le_of_quadratic_upper (A : E →L[ℝ] E) {L : ℝ}
    (hA : ∀ v : E, inner ℝ v (A v) ≤ L * ‖v‖ ^ 2) :
    LinearMap.trace ℝ E A.toLinearMap ≤ L * Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    ∑ i, inner ℝ (b i) (A (b i)) ≤ ∑ _i : Fin (Module.finrank ℝ E), L := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [b.orthonormal.norm_eq_one i, one_pow, mul_one] using hA (b i)
    _ = _ := by simp [mul_comm]

end OAI.Analysis.PDE.Elliptic
