import OAI.AlgebraicGeometry.Comparison.Betti.Open.AntiholomorphicContraction
import OAI.AlgebraicGeometry.Comparison.Betti.VectorAntiholomorphicDerivative

/-! # Form Antiholomorphic Directions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.FormAntiholomorphicDirections.Dolbeault

noncomputable section

/-! A closed form whose contraction vanishes is holomorphic in that
constant tangent direction. This follows from the actual Cartan formula. -/

open _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {U : Opens E}

theorem vectorAntiDerivative_ofRaw (n : ℕ) (f : Analysis.DifferentialForms.Manifold.Basic.RawForm E n)
    (hf : ContDiffOn ℝ ∞ f (U : Set E)) (x : U) (v : E) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw U f hf).extension x v =
      VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative f x v := by
  unfold VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative
  rw [(Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_ofRaw_eventuallyEq f hf x).fderiv_eq]

theorem closed_openForm_antiDerivative_zero (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction U n v a = 0) (x : U) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative a.extension x v = 0 := by
  have h := Open.AntiholomorphicContraction.Dolbeault.openDolbeaultD_antiContraction n v a x
  rw [hv, ha, map_zero, map_zero, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply, zero_add] at h
  exact h.symm

theorem closed_openForm_contraction_antiDerivative_zero (n : ℕ) (v w : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction U n v a = 0) (x : U) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (fun y => AntiholomorphicContraction.Dolbeault.antiContraction n w (a.extension y)) x v = 0 := by
  rw [VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative_map (AntiholomorphicContraction.Dolbeault.antiContraction n w)
    ((a.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)),
    closed_openForm_antiDerivative_zero n v a ha hv x, map_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.FormAntiholomorphicDirections.Dolbeault
