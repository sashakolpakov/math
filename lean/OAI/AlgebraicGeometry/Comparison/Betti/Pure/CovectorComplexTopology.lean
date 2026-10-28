import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexEquiv
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Covector Complex Topology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexTopology.Holomorphic

noncomputable section

/-! The genuine complex coefficient space of pure holomorphic covectors has the same norm. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

def pureCovectorComplexIsometry (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 ≃ₗᵢ[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ) where
  toLinearEquiv := CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n
  norm_map' ω := by
    have hr : (CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n ω).restrictScalars ℝ = ω.val := by
      ext v
      rfl
    calc
      ‖CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n ω‖ =
          ‖(CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n ω).restrictScalars ℝ‖ :=
        (ContinuousAlternatingMap.norm_restrictScalars (𝕜' := ℝ)
          (f := CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n ω)).symm
      _ = ‖ω‖ := congrArg norm hr

def complexCovectorToMultilinear (n : ℕ) :
    (E [⋀^Fin n]→L[ℂ] ℂ) →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => E) ℂ where
  toFun ω := ω.toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem complexCovectorToMultilinear_injective (n : ℕ) :
    Function.Injective (complexCovectorToMultilinear (E := E) n) := by
  intro ω η h
  ext v
  exact congrArg (fun f : MultilinearMap ℂ (fun _ : Fin n => E) ℂ => f v) h

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem complexCovectors_finiteDimensional [FiniteDimensional ℂ E] (n : ℕ) :
    FiniteDimensional ℂ (E [⋀^Fin n]→L[ℂ] ℂ) :=
  FiniteDimensional.of_injective (complexCovectorToMultilinear (E := E) n)
    (complexCovectorToMultilinear_injective n)

theorem pureCovectors_finiteDimensional [FiniteDimensional ℂ E] (n : ℕ) :
    FiniteDimensional ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) := by
  have h := complexCovectors_finiteDimensional (E := E) n
  exact FiniteDimensional.of_injective (CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n).toLinearMap
    (CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n).injective

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexTopology.Holomorphic
