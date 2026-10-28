import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Smooth Scalar Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothScalarExtension.Godement

noncomputable section

/-! A smooth scalar function on an open submanifold has an ambient representative smooth on precisely that open domain. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def openSmoothScalarExtension (O : Opens M) (f : O → ℂ) : M → ℂ :=
  Subtype.val.extend f 0

theorem openSmoothScalarExtension_apply (O : Opens M) (f : O → ℂ) (x : O) :
    openSmoothScalarExtension O f x.val = f x :=
  congrFun (Function.extend_comp Subtype.val_injective f 0) x

theorem openSmoothScalarExtension_smoothOn (O : Opens M) (f : O → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (openSmoothScalarExtension O f) O := by
  intro x hx
  have he : (fun y : O => openSmoothScalarExtension O f y.val) = f :=
    funext (openSmoothScalarExtension_apply O f)
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞
      (fun y : O => openSmoothScalarExtension O f y.val) ⟨x, hx⟩ := by
    rw [he]
    exact hf ⟨x, hx⟩
  exact (contMDiffAt_subtype_iff.mp hs).contMDiffWithinAt

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothScalarExtension.Godement
