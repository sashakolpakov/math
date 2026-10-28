import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexTopology
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Covector Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorCoordinates.Holomorphic

noncomputable section

/-! Finite coordinate evaluations determine the actual pure holomorphic covectors. -/

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (b : Module.Basis ι ℂ E) (n : ℕ)

def pureCovectorCoordinates : Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 →ₗ[ℂ] ((Fin n → ι) → ℂ) where
  toFun covector v := covector.val (fun i => b (v i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pureCovectorCoordinates_injective : Function.Injective (pureCovectorCoordinates b n) := by
  intro a c h
  have hm : CovectorComplexEquiv.Holomorphic.pureCovectorComplexMultilinearMap a.val a.property =
      CovectorComplexEquiv.Holomorphic.pureCovectorComplexMultilinearMap c.val c.property := by
    apply Module.Basis.ext_multilinear (fun _ : Fin n => b)
    intro v
    exact congrFun h v
  apply Subtype.ext
  ext v
  exact congrArg (fun P : MultilinearMap ℂ (fun _ : Fin n => E) ℂ => P v) hm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorCoordinates.Holomorphic
