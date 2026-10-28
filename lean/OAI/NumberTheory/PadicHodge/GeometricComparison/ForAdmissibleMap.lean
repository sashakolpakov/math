import OAI.NumberTheory.PadicHodge.GeometricComparison.SummandForFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.WeilPolynomial
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.PolynomialWeights

/-! # For Admissible Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The complete original target follows from a geometrically justified, endomorphism-natural admissible comparison. The comparison is not fixed to the existential witness selected from Cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.comparisonTarget_of_admissible_comparison
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hCompletion : Completion.GeometricWeightInput.{0})
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0}) (hBettiComparison : Betti.ComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (hnat : ∀ (f : A.ExtendingEndomorphism) (x : A.Crystalline),
      cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x))
    (hWA : letI : FiniteDimensional ℚ_[q] A.DeRham := A.deRham_finite_of_Cohomology hCohomology
      Linear.WeaklyAdmissible q A.finiteFiltration
        (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp (A.crystallineFrobeniusEquiv hCohomology))) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  let hD : FiniteDimensional ℚ_[q] A.DeRham := A.deRham_finite_of_Cohomology hCohomology
  let : FiniteDimensional ℚ_[q] A.DeRham := hD
  obtain ⟨hC, W, hW, hCW⟩ := A.native_sharedPolynomial_of_IntegralComparison hIntegralComparison ℓ hℓq
  let : FiniteDimensional ℚ_[q] A.Crystalline := hC
  let φ := A.crystallineFrobeniusEquiv hCohomology
  let φdR := WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ
  have hcomm (f : A.ExtendingEndomorphism) : Commute (A.deRhamPullback f) φdR.toLinearMap :=
    HeckeCommutation.GeneralizedHecke.conjugate_commutes cmp (A.crystallinePullback f) (A.deRhamPullback f)
      φ (hnat f) (A.crystallinePullback_commutes_equiv hCohomology f)
  refine ⟨hD, hC, cmp, φ, A.finiteFiltration,
    A.crystallineFrobeniusEquiv_toLinearMap hCohomology, rfl, hWA, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨hnat f, ?_, A.deRhamPullback_preservesFil f⟩
    intro x
    exact DFunLike.congr_fun (A.crystallinePullback_commutes_equiv hCohomology f).symm.eq x
  · exact ⟨W, hW, hCW, A.native_polynomial_weights hCompletion ℓ hℓq W hW⟩
  · exact A.algebraic_filtered_comparisons hBettiComparison (jComplex.comp κ) P
  · exact A.summandComparison_for_frobenius hBettiComparison κ jComplex ι hplace ρ P φdR hcomm hWA

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
