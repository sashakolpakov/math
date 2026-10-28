import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.BettiFinite
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.BaseChangeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalarNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandTransport

/-! # Complex Betti -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The native rational and complex Betti groups are related by actual scalar extension, naturally for every extending endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

def Geometry.AbelianH1Model.rationalComplexBettiEquiv : (ℂ ⊗[ℚ] A.Betti j) ≃ₗ[ℂ] A.ComplexBetti j := by
  letI : FiniteDimensional ℚ (A.Betti j) := A.rationalBetti_finiteDimensional j P
  letI : FiniteDimensional ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (AlgebraicGeometry.Betti.Scheme.schemePointSpace (A.complexFiber j).scheme)).homology 1) :=
    SingularFinitenessOf.SingularFiniteness.homology_of_cohomology ℚ _ 1
  exact Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv ℚ ℂ _ 1

theorem Geometry.AbelianH1Model.rationalComplexBettiEquiv_pullback (f : A.ExtendingEndomorphism) (x : ℂ ⊗[ℚ] A.Betti j) :
    A.rationalComplexBettiEquiv j P ((A.bettiPullback j f).baseChange ℂ x) =
      A.complexBettiPullback j f (A.rationalComplexBettiEquiv j P x) := by
  let : FiniteDimensional ℚ (A.Betti j) := A.rationalBetti_finiteDimensional j P
  let : FiniteDimensional ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (AlgebraicGeometry.Betti.Scheme.schemePointSpace (A.complexFiber j).scheme)).homology 1) :=
    SingularFinitenessOf.SingularFiniteness.homology_of_cohomology ℚ _ 1
  exact Cohomology.BaseChangeNaturality.ChainScalarExtension.tensorCohomologyEquiv_naturality ℚ ℂ
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (A.complexEndomorphism j f)) 1 x

theorem Geometry.AbelianH1Model.rationalComplexBettiEquiv_hecke {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) (h : H) (x : ℂ ⊗[ℚ] A.Betti j) :
    A.rationalComplexBettiEquiv j P ((A.bettiHecke j ρ h).baseChange ℂ x) =
      A.complexBettiHecke j ρ h (A.rationalComplexBettiEquiv j P x) :=
  HeckeScalarNaturality.GeneralizedHecke.weighted_scalar_naturality (A.rationalComplexBettiEquiv j P)
    (ρ.presentation h) (A.bettiPullback j) (A.complexBettiPullback j)
    (A.rationalComplexBettiEquiv_pullback j P) x

theorem Geometry.AbelianH1Model.rationalComplexBettiEquiv_summand {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) (χ : H → ℂ) :
    (Linear.generalizedHeckeSummand (fun h => (A.bettiHecke j ρ h).baseChange ℂ) χ).map
        (A.rationalComplexBettiEquiv j P).toLinearMap = A.bettiHeckeSummand j ρ χ :=
  HeckeSummandTransport.GeneralizedHecke.summand_map (A.rationalComplexBettiEquiv j P) _ _
    (A.rationalComplexBettiEquiv_hecke j P ρ) χ

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
