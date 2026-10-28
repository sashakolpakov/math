import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.NewtonEquality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.WeilPolynomial

/-! # Newton -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Equality of the original geometric Hodge and Newton numbers from Cohomology, Completion, IntegralComparison, and BettiComparison, with all polynomial-existence and projectivity obligations discharged geometrically. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Geometry.AbelianH1Model.native_geometric_hodge_newton_equality
    {K : Type} [Field K] [NumberField K]
    {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hCompletion : Completion.GeometricWeightInput.{0})
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0}) (hBettiComparison : Betti.ComparisonInput)
    (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI : FiniteDimensional ℚ_[q] A.DeRham := A.deRham_finite_of_Cohomology hCohomology
    A.finiteFiltration.tH = (Padic.valuation (A.deRhamFrobeniusEquiv hCohomology).toLinearMap.det : ℚ) := by
  let : FiniteDimensional ℚ_[q] A.DeRham := A.deRham_finite_of_Cohomology hCohomology
  obtain ⟨hC, W, hW, hCW⟩ := A.native_sharedPolynomial_of_IntegralComparison hIntegralComparison ℓ hℓq
  let : FiniteDimensional ℚ_[q] A.Crystalline := hC
  exact A.native_hodge_newton_equality hCohomology hCompletion hBettiComparison j P ℓ hℓq W hW hCW

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
