import OAI.AlgebraicGeometry.Comparison.Betti.AlternatingCovectors
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Iterated Covector Determinant -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IteratedCovectorDeterminant.Smooth

noncomputable section

/-! The preserved iterated covector wedge is the ordinary determinant of its one-covector evaluations. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedCovectorWedge_eq_det (n : ℕ) (c : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) (v : Fin n → E) :
    AlternatingCovectors.Smooth.iteratedCovectorWedge n c a v =
      c * (Matrix.of (fun i j => a j (fun _ => v i))).det := by
  rw [AlternatingCovectors.Smooth.iteratedCovectorWedge_apply, Matrix.det_apply]
  simp only [AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum, AlternatingCovectors.Smooth.covectorTensorValue, Function.comp_apply, Matrix.of_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.IteratedCovectorDeterminant.Smooth
