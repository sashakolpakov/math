import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Reflection
import OAI.Analysis.PDE.Elliptic.Boundary.NormalJet

/-! The exact boundary jets that make odd reflection twice differentiable. -/

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Elliptic OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem flat_boundary_hessian_zero (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (e x v w : E) (he : ‖e‖ = 1) (hx : inner ℝ e x = 0)
    (hv : inner ℝ e v = 0) (hw : inner ℝ e w = 0)
    (hzero : ∀ y, inner ℝ e y = 0 → u y = 0) :
    fderiv ℝ (fderiv ℝ u) x v w = 0 := by
  let ell : E →L[ℝ] ℝ := innerSL ℝ e
  have hell : ell ≠ 0 := by
    intro hh
    have hee := congrArg (fun L : E →L[ℝ] ℝ => L e) hh
    have hn : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    exact one_ne_zero (hn.symm.trans (by simpa [ell] using hee))
  have hl : ∀ᶠ y in 𝓝 x, ell y = ell x → u y = 0 := by
    filter_upwards [] with y hy
    exact hzero y (hy.trans hx)
  obtain ⟨a, ha⟩ := OAI.Analysis.PDE.Dirichlet.level_set_gradient_factor
    (by simpa only [ell.hasFDerivAt.fderiv] using ell.hasStrictFDerivAt (x := x))
    (by simpa only [ell.hasFDerivAt.fderiv] using hell) (hu.differentiable (by norm_num) x) hl
  have hder : fderiv ℝ (ell : E → ℝ) = fun _ => ell := funext fun y => ell.hasFDerivAt.fderiv
  have hh := OAI.Analysis.PDE.Dirichlet.level_set_tangent_hessian (x := x) (v := v) (z := w) ell.contDiff hu
    (by simpa only [hder] using hell) hl ha
    (by rw [hder]; exact hv) (by rw [hder]; exact hw)
  simpa [hder] using hh

omit [FiniteDimensional ℝ E] in
theorem boundary_bilinear_reflection (e : E) (he : ‖e‖ = 1)
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (ht : ∀ v w, inner ℝ e v = 0 → inner ℝ e w = 0 → H v w = 0)
    (hn : H e e = 0) (v w : E) :
    H (normalReflection e v) (normalReflection e w) = -H v w := by
  have hp := ht (normalProjection e v) (normalProjection e w)
    (inner_normalProjection e v he) (inner_normalProjection e w he)
  simp only [normalProjection, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul, hn, mul_zero, sub_zero] at hp
  rw [normalReflection_apply e v he, normalReflection_apply e w he]
  simp only [map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul, hn, mul_zero, sub_zero]
  nlinarith only [hp]

theorem boundary_first_reflection (u : E → ℝ) (hu : Differentiable ℝ u)
    (e x : E) (he : ‖e‖ = 1) (hx : inner ℝ e x = 0)
    (hzero : ∀ y, inner ℝ e y = 0 → u y = 0) (v : E) :
    fderiv ℝ u x (normalReflection e v) = -fderiv ℝ u x v := by
  have hf := OAI.Analysis.PDE.Elliptic.flat_boundary_fderiv_eq_normal (hu x) he hx (Filter.Eventually.of_forall hzero)
  rw [hf]
  change (fderiv ℝ u x e) * inner ℝ e (normalReflection e v) =
    -((fderiv ℝ u x e) * inner ℝ e v)
  rw [inner_normalReflection e v he]
  ring

end OAI.Analysis.PDE.Schauder
