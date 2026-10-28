import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative

/-! # Poincare Locality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.PoincareLocality

noncomputable section

/-!
# Translation and locality for the radial primitive

These facts permit the global radial formula to construct primitives locally
around an arbitrary point. A form need only vanish on the radial segments for
its radial homotopy to vanish there.
-/

open Set _root_.MeasureTheory _root_.ContinuousAlternatingMap
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace SmoothForm

/-- Translate the coefficients of an actual smooth form. The derivative of a
translation is the identity on tangent vectors. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate (c : E) (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n :=
  ⟨fun y => form (c + y), form.smooth.comp (contDiff_const.add contDiff_id)⟩

@[simp] theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate_apply (c : E) (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) (y : E) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate c form y = form (c + y) := rfl

/-- Exterior differentiation commutes with translation. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_translate (c : E) (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate c form) = Analysis.DifferentialForms.Manifold.Basic.SmoothForm.translate c (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d form) := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro y
  change extDeriv (fun z => form (c + z)) y = extDeriv (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E n) (c + y)
  have htranslation : HasFDerivAt (fun z : E => c + z) (ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).const_add c
  have hderiv : fderiv ℝ (fun z => form (c + z)) y =
      fderiv ℝ (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E n) (c + y) := by
    have h := ((form.smooth.differentiable (by simp) (c + y)).hasFDerivAt.comp y
      htranslation).fderiv
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using h
  simp only [extDeriv, hderiv]

end SmoothForm

/-- The radial homotopy of a form vanishing on a star-convex set vanishes on
that set. No regularity beyond the stated equality is required. -/
theorem radialHomotopy_eq_zero_on_starConvex
    {form : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)} {S : Set E} (hS : StarConvex ℝ (0 : E) S)
    (hform : EqOn form 0 S) {x : E} (hx : x ∈ S) :
    RadialOne.radialHomotopy form x = 0 := by
  unfold RadialOne.radialHomotopy
  calc
    (∫ t in (0 : ℝ)..1, RadialOne.radialIntegrand form x t) = ∫ _t in (0 : ℝ)..1, (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      have hz := hform (hS.smul_mem hx ht'.1 ht'.2)
      dsimp only
      simp only [RadialOne.radialIntegrand, hz, Pi.zero_apply, curryLeft_zero,
        _root_.zero_apply, smul_zero]
    _ = 0 := by simp

end

end OAI.AlgebraicTopology.DeRham.Comparison.PoincareLocality
