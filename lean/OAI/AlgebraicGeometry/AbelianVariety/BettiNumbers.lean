import OAI.AlgebraicGeometry.AbelianVariety.DeRham
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Betti Numbers -/

namespace OAI.AlgebraicGeometry.AbelianVariety.BettiNumbers.Constructions.ExteriorCohomology

noncomputable section

open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj TensorProduct

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def covectorCoordinatesEquiv (n : ℕ) :
    (E [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ]
      (Fin (Module.finrank ℝ (⋀[ℝ]^n E)) → ℂ) :=
  (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n).trans ((Module.finBasis ℝ (⋀[ℝ]^n E)).constr ℂ).symm

theorem finiteDimensional_covectors (n : ℕ) :
    FiniteDimensional ℂ (E [⋀^Fin n]→L[ℝ] ℂ) :=
  Module.Finite.equiv (covectorCoordinatesEquiv E n).symm

theorem finrank_covectors (n : ℕ) :
    Module.finrank ℂ (E [⋀^Fin n]→L[ℝ] ℂ) = (Module.finrank ℝ E).choose n := by
  rw [(covectorCoordinatesEquiv E n).finrank_eq]
  simp [exteriorPower.finrank_eq]

theorem abelian_complex_betti_number (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Module.finrank ℂ (A.variety.complexCohomology n) =
      (2 * A.variety.complexDimension).choose n := by
  rw [← (DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A n).finrank_eq, finrank_covectors,
    A.variety.analyticModel_real_finrank]

theorem abelian_rational_betti_number (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Module.finrank ℚ (A.variety.rationalCohomology n) =
      (2 * A.variety.complexDimension).choose n := by
  let : Module.Finite ℚ (A.variety.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety n
  have he := (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv
    (Betti.Scheme.schemePointSpace A.toOver) n).finrank_eq
  rw [Module.finrank_baseChange] at he
  exact he.trans (abelian_complex_betti_number A n)

theorem abelian_h1_finrank (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Module.finrank ℚ (A.variety.rationalCohomology 1) =
      2 * A.variety.complexDimension := by
  simpa using abelian_rational_betti_number A 1

end

end OAI.AlgebraicGeometry.AbelianVariety.BettiNumbers.Constructions.ExteriorCohomology
