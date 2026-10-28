import OAI.Analysis.HodgeTheory.Decomposition.Multiplication
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Multiplier -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Multiplier.Constructions

noncomputable section

/-! Smooth scalar multiplication extended to the actual completed form L²
space using its proved norm estimate. -/

open scoped ContDiff _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)

theorem projective_smooth_multiplier_bound :
    ∃ C : ℝ, ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      ‖Form.Constructions.smoothToProjectiveL2 V n (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)‖ ≤
        C * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by
  obtain ⟨C, hC⟩ := (HasCompactSupport.of_compactSpace f).exists_bound_of_continuous hf.continuous
  exact ⟨max C 0, fun a => Multiplication.Constructions.smoothToProjectiveL2_function_norm_bound V n f hf (max C 0)
    (le_max_right _ _) (fun x => (hC x).trans (le_max_left _ _)) a⟩

/-- Multiplication by a smooth function on the genuine L² Hilbert completion. -/
def projectiveL2Multiplier : Form.Constructions.ProjectiveL2Forms V n →L[ℂ] Form.Constructions.ProjectiveL2Forms V n :=
  ((Form.Constructions.smoothToProjectiveL2 V n).comp (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf)).extendOfNorm
    (Form.Constructions.smoothToProjectiveL2 V n)

theorem projectiveL2Multiplier_on_smooth
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveL2Multiplier V n f hf (Form.Constructions.smoothToProjectiveL2 V n a) =
      Form.Constructions.smoothToProjectiveL2 V n (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a) := by
  exact LinearMap.extendOfNorm_eq (Form.Constructions.smoothToProjectiveL2_dense V n)
    (projective_smooth_multiplier_bound V n f hf) a

end

end OAI.Analysis.HodgeTheory.Decomposition.Multiplier.Constructions
