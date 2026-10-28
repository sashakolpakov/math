import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.NaturalityCriterion
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Admissibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.ForAdmissibleMap

/-! # Criterion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Assemble the exact conditional target from a proved integral
naturality identity for the actual constructed comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.comparisonTarget_of_native_integral_naturality
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hCompletion : Completion.GeometricWeightInput.{0})
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0}) (hBettiComparison : Betti.ComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (hNat : ∀ (f : A.ExtendingEndomorphism)
      (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1),
      A.constructedIntegralCrystallineEquiv (A.integralDeRhamPullback f x) =
        IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q (A.specialEndomorphism f)
          (A.constructedIntegralCrystallineEquiv x)) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ :=
  A.comparisonTarget_of_admissible_comparison hCohomology hCompletion hIntegralComparison hBettiComparison κ jComplex ι hplace ρ P ℓ hℓq
    A.constructedCrystallineDeRhamEquiv
    (fun f x => A.constructedCrystallineDeRhamEquiv_naturality_of_integral f (hNat f) x)
    (A.constructedComparison_weaklyAdmissible hCohomology hCompletion hIntegralComparison hBettiComparison (jComplex.comp κ) P ℓ hℓq)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
