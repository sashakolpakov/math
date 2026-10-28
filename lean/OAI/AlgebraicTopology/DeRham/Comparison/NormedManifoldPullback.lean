import OAI.Analysis.DifferentialForms.Manifold.NormedSpace
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws
import OAI.Analysis.DifferentialForms.Manifold.Vectors

/-! # Normed Manifold Pullback -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.NormedManifoldPullback

noncomputable section

/-!
# Agreement of the actual normed and manifold pullbacks

The identity-chart formula identifies manifold pullback on a normed space with
ordinary pullback by the Fréchet derivative. This is proved from the tangent
chain rule, not imposed as an additional comparison field.
-/

open scoped _root_.Manifold ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

/-- In the canonical atlases, manifold pullback is the ordinary derivative pullback. -/
theorem toNormedSpace_pullback_self (g : E → F) (hg : ContDiff ℝ ∞ g)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F F n) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg.contMDiff form).toNormedSpace =
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback g hg form.toNormedSpace := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  change ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F F n).pullback g).toNormedSpace x =
    ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F F n).toNormedSpace (g x)).compContinuousLinearMap
      (fderiv ℝ g x)
  have h := (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F F n).pullback_inChart g
    (OpenPartialHomeomorph.refl E) (OpenPartialHomeomorph.refl F)
    (by simp) (by simp) (y := x) (by simp) (by simp)
    ((hg.contMDiff.mdifferentiable (by simp)) x)
  simpa only [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_refl, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, Function.id_comp, Function.comp_id, id_eq] using h

end

end OAI.AlgebraicTopology.DeRham.Comparison.NormedManifoldPullback
