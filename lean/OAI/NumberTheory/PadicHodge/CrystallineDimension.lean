import OAI.NumberTheory.PadicHodge.ProjectiveDeRhamFactorized
import OAI.NumberTheory.PadicHodge.BettiProductDimension
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Crystalline
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianGlobalFilteredComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FiniteScalarExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingAdditivity

/-! # Crystalline Dimension -/

namespace OAI.NumberTheory.PadicHodge.CrystallineDimension.FrobeniusSlope

noncomputable section

/-! Dimensions of actual crystalline H1 using the constructed comparison
and restricted projective comparison. No operator naturality is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductComparisonModel.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

/-- The projective comparison starts from the original number-field object. -/
def algebraicBettiEquiv : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j :=
  (A.complexAlgebraicComparison j).trans
    (ProjectiveDeRhamFactorized.FrobeniusSlope.nativeBettiEquiv (A.complexFiber j).scheme P 1)

include j P

theorem betti_finite : FiniteDimensional ℂ (A.ComplexBetti j) := by
  let B := AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingAdditivity.CM.complexAbelianVariety A j P
  let : FiniteDimensional ℚ (B.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite B.variety 1
  exact Module.Finite.equiv (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) 1)

theorem algebraic_finite : FiniteDimensional K A.AlgebraicDeRham := by
  let : Algebra K ℂ := j.toAlgebra
  let : FiniteDimensional ℂ (A.ComplexBetti j) := betti_finite A j P
  exact GeometricComparison.Finite.FiniteScalarExtension.ScalarExtension.finite_of_comparison K ℂ A.AlgebraicDeRham (algebraicBettiEquiv A j P)

theorem deRham_finite : FiniteDimensional ℚ_[q] A.DeRham := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : FiniteDimensional K A.AlgebraicDeRham := algebraic_finite A j P
  exact A.localAlgebraicComparison.finiteDimensional

theorem crystalline_finite : FiniteDimensional ℚ_[q] A.Crystalline := by
  let : FiniteDimensional ℚ_[q] A.DeRham := deRham_finite A j P
  exact A.constructedCrystallineDeRhamEquiv.symm.finiteDimensional

theorem crystalline_finrank_eq_betti :
    Module.finrank ℚ_[q] A.Crystalline = Module.finrank ℂ (A.ComplexBetti j) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : Algebra K ℂ := j.toAlgebra
  let : FiniteDimensional K A.AlgebraicDeRham := algebraic_finite A j P
  have hl : Module.finrank ℚ_[q] A.DeRham = Module.finrank K A.AlgebraicDeRham :=
    A.localAlgebraicComparison.finrank_eq.symm.trans Module.finrank_baseChange
  have hc : Module.finrank ℂ (A.ComplexBetti j) = Module.finrank K A.AlgebraicDeRham :=
    (algebraicBettiEquiv A j P).finrank_eq.symm.trans Module.finrank_baseChange
  exact A.constructedCrystallineDeRhamEquiv.finrank_eq.trans (hl.trans hc.symm)

end

end OAI.NumberTheory.PadicHodge.CrystallineDimension.FrobeniusSlope
