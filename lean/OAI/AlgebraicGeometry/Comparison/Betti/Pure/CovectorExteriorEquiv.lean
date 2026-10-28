import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorDual
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.MultilinearContinuity
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Covector Exterior Equiv -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorEquiv.Holomorphic

noncomputable section

/-! Actual pure covectors are canonically the dual of the complex exterior power in every degree. -/

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem pureCovectorExteriorDualMap_surjective (n : ℕ) :
    Function.Surjective (CovectorExteriorDual.Holomorphic.pureCovectorExteriorDualMap E n) := by
  intro f
  let a : E [⋀^Fin n]→ₗ[ℂ] ℂ :=
    (exteriorPower.alternatingMapLinearEquiv (R := ℂ) (M := E) (N := ℂ)).symm f
  let c : E [⋀^Fin n]→L[ℂ] ℂ :=
    { a with cont := Finite.MultilinearContinuity.LinearAlgebra.multilinear_continuous n a.toMultilinearMap }
  refine ⟨(CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n).symm c, ?_⟩
  change exteriorPower.alternatingMapLinearEquiv
    ((CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n ((CovectorComplexEquiv.Holomorphic.pureCovectorComplexEquiv E n).symm c)).toAlternatingMap) = f
  rw [LinearEquiv.apply_symm_apply]
  exact (exteriorPower.alternatingMapLinearEquiv (R := ℂ) (M := E) (N := ℂ)).apply_symm_apply f

def pureCovectorExteriorDualEquiv (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 ≃ₗ[ℂ] Module.Dual ℂ (⋀[ℂ]^n E) :=
  LinearEquiv.ofBijective (CovectorExteriorDual.Holomorphic.pureCovectorExteriorDualMap E n)
    ⟨CovectorExteriorDual.Holomorphic.pureCovectorExteriorDualMap_injective E n, pureCovectorExteriorDualMap_surjective E n⟩

theorem pureCovector_finrank (n : ℕ) :
    Module.finrank ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) = (Module.finrank ℂ E).choose n := by
  rw [(pureCovectorExteriorDualEquiv E n).finrank_eq, Subspace.dual_finrank_eq,
    exteriorPower.finrank_eq]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorEquiv.Holomorphic
