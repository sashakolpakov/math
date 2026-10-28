import OAI.Analysis.Normed.Function.Sobolev.Reflection.Test

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

variable {d N : ℕ}

theorem reflection_weight_cancel (k i : Fin d) {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    (c * (if i = k then a else 1) * |a⁻¹|) *
      (if i = k then a⁻¹ else 1) = c * |a⁻¹| := by
  by_cases hi : i = k
  · simp only [hi,ite_true]
    field_simp
  · simp [hi]

theorem reflectionTest_boundary (k : Fin d) (a c : Fin N → ℝ)
    (ha : ∀j, a j < 0) (hc : ∑j, c j = 1)
    (φ : (Fin d → ℝ) → ℝ) {x : Fin d → ℝ} (hx : x k = 0) :
    reflectionTest k a (fun j ↦ c j * a j * |(a j)⁻¹|) φ x = 0 := by
  have he (j : Fin N) : c j * a j * |(a j)⁻¹| = -c j := by
    rw [abs_of_neg (inv_neg''.mpr (ha j))]
    field_simp [(ha j).ne]
  simp only [reflectionTest,normalScale_on_boundary k _ hx,he,neg_mul,
    Finset.sum_neg_distrib,← Finset.sum_mul,hc,one_mul,add_neg_cancel]

/-- Finite reflection preserves a genuine weak derivative. The sole
matching condition is the zeroth moment in the normal direction. -/
theorem hasWeakDirectionalDerivative_reflection
    (k i : Fin d) (a c : Fin N → ℝ) (ha : ∀j, a j < 0)
    (hc : i = k → ∑j, c j = 1)
    {u g : (Fin d → ℝ) → ℝ} (hu : Integrable u) (hg : Integrable g)
    (hd : OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn volume {x | 0 < x k} (Pi.single i 1) u g) :
    OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume (Pi.single i 1)
      (reflectionExtension k a c u)
      (reflectionExtension k a (fun j ↦ c j * (if i = k then a j else 1)) g) := by
  intro φ hφ hs
  let c' : Fin N → ℝ := fun j ↦ c j * (if i = k then a j else 1)
  let b : Fin N → ℝ := fun j ↦ c' j * |(a j)⁻¹|
  let ψ := reflectionTest k a b φ
  have hψ : ContDiff ℝ 1 ψ := contDiff_reflectionTest k a b hφ
  have hψs : HasCompactSupport ψ :=
    hasCompactSupport_reflectionTest k a b (fun j ↦ (ha j).ne) hs
  have hbdy : (Pi.single i (1 : ℝ) : Fin d → ℝ) k = 0 ∨ ∀x, x k = 0 → ψ x = 0 := by
    by_cases hik : i = k
    · right
      intro x hx
      simpa only [ψ,b,c',hik,ite_true] using reflectionTest_boundary k a c ha (hc hik) φ hx
    · left
      simp [Ne.symm hik]
  have he := halfspace_weak_test k (Pi.single i 1) hu hg hd ψ hψ hψs hbdy
  have hder (x : Fin d → ℝ) : fderiv ℝ ψ x (Pi.single i 1) =
      reflectionTest k a (fun j ↦ c j * |(a j)⁻¹|)
        (fun y ↦ fderiv ℝ φ y (Pi.single i 1)) x := by
    rw [reflectionTest_derivative k i a b hφ]
    congr 2
    funext j
    exact reflection_weight_cancel k i (ha j).ne (c j)
  have hφd : Continuous (fun x ↦ fderiv ℝ φ x (Pi.single i 1)) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφds : HasCompactSupport (fun x ↦ fderiv ℝ φ x (Pi.single i 1)) :=
    hs.fderiv_apply ℝ _
  simp_rw [hder] at he
  rw [integral_mul_reflectionTest k a b (fun j ↦ (ha j).ne) hg hφ.continuous hs,
    integral_mul_reflectionTest k a _ (fun j ↦ (ha j).ne) hu hφd hφds] at he
  simp only [RCLike.inner_apply,conj_trivial,mul_comm]
  simp_rw [mul_comm (φ _) (reflectionExtension k a _ g _)]
  rw [integral_reflectionExtension_mul k a _ ha hg hφ.continuous hs,
    integral_reflectionExtension_mul k a c ha hu hφd hφds]
  exact he

end OAI.Analysis.Normed.Function.Sobolev
