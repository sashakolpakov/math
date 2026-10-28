import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarPotentialFunctions
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf

/-! # Global Real Scalar Form -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalRealScalarForm

noncomputable section

/-! An actual smooth real scalar function as an original global real zero-form. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)

def globalRealScalarForm : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (SmoothScalarForm.smoothScalarOpenZeroForm
    (⟨fun x : (⊤ : TopologicalSpace.Opens M) => (f x.val : ℂ),
      Complex.ofRealCLM.contDiff.contMDiff.comp (hf.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E))))⟩ :
        SmoothScalarForm.SmoothComplexOpenFunction (E := E) ⊤))

theorem globalRealScalarForm_apply (x : M) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x) :
    globalRealScalarForm f hf x v = (f x : ℂ) := by
  rw [globalRealScalarForm, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply, SmoothScalarForm.smoothScalarOpenZeroForm_apply]
  rfl

theorem globalRealScalarForm_real : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (globalRealScalarForm f hf) = globalRealScalarForm f hf := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change star (globalRealScalarForm f hf x v) = globalRealScalarForm f hf x v
  rw [globalRealScalarForm_apply]
  exact Complex.conj_ofReal (f x)

theorem globalRealScalarForm_scalar (x : M) : ScalarPotentialFunctions.realPotentialScalar (globalRealScalarForm f hf) x = f x :=
  (congrArg Complex.re (globalRealScalarForm_apply f hf x 0)).trans (Complex.ofReal_re (f x))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalRealScalarForm
