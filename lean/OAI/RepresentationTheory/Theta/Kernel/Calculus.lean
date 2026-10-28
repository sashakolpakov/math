import Mathlib

/-! # Calculus -/

namespace OAI.RepresentationTheory.Theta.Kernel.Calculus

noncomputable section

open scoped BigOperators

abbrev Covector2 := Fin 2 → ℂ
abbrev TensorCoordinates := (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ

def doubleAlt (h : TensorCoordinates) : ℂ :=
  (h (0, 0) (1, 1) - h (1, 0) (0, 1)
    - h (0, 1) (1, 0) + h (1, 1) (0, 0)) / 2

def wedgeCoefficient (a b : Covector2) : ℂ :=
  a 0 * b 1 - a 1 * b 0

lemma exists_wedge_ne_zero {I₁ I₂ : Type*}
    (f : I₁ → Covector2) (g : I₂ → Covector2)
    (hf : Submodule.span ℂ (Set.range f) = ⊤)
    (hg : Submodule.span ℂ (Set.range g) = ⊤) :
    ∃ i j, wedgeCoefficient (f i) (g j) ≠ 0 := by
  classical
  by_contra! h
  have hleft : ∀ a ∈ Submodule.span ℂ (Set.range f),
      ∀ j, wedgeCoefficient a (g j) = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
    | zero => intro j; simp [wedgeCoefficient]
    | add x y _ _ hx hy =>
        intro j
        dsimp [wedgeCoefficient] at *
        linear_combination hx j + hy j
    | smul c x _ hx =>
        intro j
        dsimp [wedgeCoefficient] at *
        linear_combination c * hx j
  have hall : ∀ a b : Covector2, wedgeCoefficient a b = 0 := by
    intro a b
    have hb : b ∈ Submodule.span ℂ (Set.range g) := by rw [hg]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact hleft a (by rw [hf]; trivial) j
    | zero => simp [wedgeCoefficient]
    | add x y _ _ hx hy =>
        dsimp [wedgeCoefficient] at *
        linear_combination hx + hy
    | smul c x _ hx =>
        dsimp [wedgeCoefficient] at *
        linear_combination c * hx
  have := hall ![1, 0] ![0, 1]
  norm_num [wedgeCoefficient] at this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma hessian_apply_eq (f : E → ℂ) (hf : ContDiff ℂ 2 f) (x v w : E) :
    iteratedFDeriv ℂ 2 f x ![v, w] =
      fderiv ℂ (fun y => fderiv ℂ f y w) x v := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

lemma hessian_mul (f g : E → ℂ)
    (hf : ContDiff ℂ 2 f) (hg : ContDiff ℂ 2 g) (x v w : E) :
    iteratedFDeriv ℂ 2 (fun y => f y * g y) x ![v, w] =
      iteratedFDeriv ℂ 2 f x ![v, w] * g x +
      fderiv ℂ f x w * fderiv ℂ g x v +
      fderiv ℂ f x v * fderiv ℂ g x w +
      f x * iteratedFDeriv ℂ 2 g x ![v, w] := by
  have hf' := hf.differentiable (by norm_num)
  have hg' := hg.differentiable (by norm_num)
  have hdf : Differentiable ℂ (fun y => fderiv ℂ f y w) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply
      (differentiable_const w)
  have hdg : Differentiable ℂ (fun y => fderiv ℂ g y w) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply
      (differentiable_const w)
  rw [hessian_apply_eq _ (hf.mul hg)]
  have heq : (fun y => fderiv ℂ (fun z => f z * g z) y w) =
      (fun y => fderiv ℂ f y w * g y + f y * fderiv ℂ g y w) := by
    funext y
    rw [fderiv_fun_mul (hf' y) (hg' y)]
    simp [mul_comm, add_comm]
  rw [heq]
  have hd := ((hdf x).hasFDerivAt.fun_mul (hg' x).hasFDerivAt).fun_add
    ((hf' x).hasFDerivAt.fun_mul (hdg x).hasFDerivAt)
  rw [hd.fderiv]
  rw [hessian_apply_eq f hf, hessian_apply_eq g hg]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

lemma mixed_hessian
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : E →L[ℂ] F) (R : E →L[ℂ] G)
    (f : F → ℂ) (g : G → ℂ)
    (hf : ContDiff ℂ 2 f) (hg : ContDiff ℂ 2 g)
    (v w : E) (hL : L w = 0) (hR : R v = 0) :
    iteratedFDeriv ℂ 2 (fun y => f (L y) * g (R y)) 0 ![v, w] =
      fderiv ℂ f 0 (L v) * fderiv ℂ g 0 (R w) := by
  have hfL : ContDiff ℂ 2 (f ∘ L) := hf.comp L.contDiff
  have hgR : ContDiff ℂ 2 (g ∘ R) := hg.comp R.contDiff
  have hLf : iteratedFDeriv ℂ 2 (f ∘ L) 0 ![v, w] = 0 := by
    rw [L.iteratedFDeriv_comp_right hf 0 le_rfl,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    apply ContinuousMultilinearMap.map_coord_zero _ 1
    simpa using hL
  have hRg : iteratedFDeriv ℂ 2 (g ∘ R) 0 ![v, w] = 0 := by
    rw [R.iteratedFDeriv_comp_right hg 0 le_rfl,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    apply ContinuousMultilinearMap.map_coord_zero _ 0
    simpa using hR
  have hdL : fderiv ℂ (f ∘ L) 0 = (fderiv ℂ f 0).comp L := by
    simpa using (hf.differentiable (by norm_num) (L 0)).hasFDerivAt.comp
      0 L.hasFDerivAt |>.fderiv
  have hdR : fderiv ℂ (g ∘ R) 0 = (fderiv ℂ g 0).comp R := by
    simpa using (hg.differentiable (by norm_num) (R 0)).hasFDerivAt.comp
      0 R.hasFDerivAt |>.fderiv
  have h := hessian_mul (f ∘ L) (g ∘ R) hfL hgR 0 v w
  simpa [hLf, hRg, hdL, hdR, hL, hR] using h

end

end OAI.RepresentationTheory.Theta.Kernel.Calculus
