import OAI.AlgebraicGeometry.Comparison.Betti.VectorAntiholomorphicDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Antiholomorphic Derivative Commutation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicDerivativeCommutation.Dolbeault

noncomputable section

/-! Antiholomorphic directional differentiation commutes with an
ordinary constant directional derivative when the actual second
Fréchet derivative is symmetric. -/

open scoped _root_.Topology ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

theorem vectorAntiDerivative_constantDerivative_commute {g : E → F} {x : E}
    (hD : DifferentiableAt ℝ (fderiv ℝ g) x) (hSym : IsSymmSndFDerivAt ℝ g x) (v w : E) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (fun y => fderiv ℝ g y v) x w =
      fderiv ℝ (fun y => VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative g y w) x v := by
  let A := ContinuousLinearMap.apply ℝ F v
  let B := (ContinuousLinearMap.apply ℝ F w).comp
    ((OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F).restrictScalars ℝ)
  have hEval : fderiv ℝ (fun y => fderiv ℝ g y v) x = A.comp (fderiv ℝ (fderiv ℝ g) x) :=
    (A.hasFDerivAt.comp x hD.hasFDerivAt).fderiv
  have hAnti : fderiv ℝ (fun y => VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative g y w) x =
      B.comp (fderiv ℝ (fderiv ℝ g) x) := (B.hasFDerivAt.comp x hD.hasFDerivAt).fderiv
  rw [VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative, hEval, hAnti, OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  change (1 / 2 : ℂ) • (fderiv ℝ (fderiv ℝ g) x w v +
      Complex.I • fderiv ℝ (fderiv ℝ g) x (Complex.I • w) v) =
    (1 / 2 : ℂ) • (fderiv ℝ (fderiv ℝ g) x v w +
      Complex.I • fderiv ℝ (fderiv ℝ g) x v (Complex.I • w))
  rw [hSym.eq w v, hSym.eq (Complex.I • w) v]

theorem vectorAntiDerivative_constantDerivative_zero {g : E → F} {x : E}
    (hg : ContDiffAt ℝ ∞ g x) (v w : E)
    (hzero : ∀ᶠ y in 𝓝 x, VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative g y w = 0) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (fun y => fderiv ℝ g y v) x w = 0 := by
  have hD := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hSym := hg.isSymmSndFDerivAt (by simp)
  rw [vectorAntiDerivative_constantDerivative_commute hD hSym]
  have he : (fun y => VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative g y w) =ᶠ[𝓝 x] (fun _ => (0 : F)) := hzero
  rw [he.fderiv_eq, (hasFDerivAt_const (0 : F) x).fderiv]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicDerivativeCommutation.Dolbeault
