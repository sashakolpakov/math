import OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopyIdentity
import OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopySmooth
import OAI.AlgebraicTopology.DeRham.Comparison.RadialLinearity
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative

/-! # Radial Smooth Poincare -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialSmoothPoincare.SmoothForm

noncomputable section

/-!
# Poincaré lemma for actual smooth forms on a finite-dimensional vector space

The primitive is the genuine radial integral. Both its smoothness and its
exterior derivative are proved by the imported analytic results.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- The standard radial homotopy, bundled as a smooth differential form. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1)) : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n :=
  ⟨RadialOne.radialHomotopy (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)),
    RadialHomotopySmooth.contDiff_radialHomotopy form.smooth⟩

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm_apply (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1)) (x : E) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm form x = RadialOne.radialHomotopy (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) x := rfl

/-- The actual radial operator is complex linear on smooth forms. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyLinear : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1) →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n where
  toFun := Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm
  map_add' form other := by
    apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
    intro x
    exact RadialLinearity.radialHomotopy_add form.smooth.continuous other.smooth.continuous x
  map_smul' c form := by
    apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
    intro x
    exact RadialLinearity.radialHomotopy_complex_smul c (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) x

/-- The bundled radial homotopy identity in every positive degree. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_radialHomotopy_add_radialHomotopy_d (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1)) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm form) + Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d form) = form := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  exact RadialHomotopyIdentity.radialHomotopy_identity (form.smooth.of_le (by simp)) x

/-- Every closed positive-degree smooth form on a real vector space is exact. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.exists_primitive (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 1)) (hclosed : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d form = 0) :
    ∃ primitive : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d primitive = form := by
  refine ⟨Analysis.DifferentialForms.Manifold.Basic.SmoothForm.radialHomotopyForm form, ?_⟩
  have hraw : extDeriv (form : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) = 0 :=
    congrArg (fun eta : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (n + 2) ↦ (eta : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 2))) hclosed
  have h := RadialHomotopyIdentity.extDeriv_radialHomotopy_of_closed
    (form.smooth.of_le (by simp)) hraw
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  exact congrFun h x

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialSmoothPoincare.SmoothForm
