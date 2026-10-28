import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Naturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Criterion

/-! # Target -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Full conditional GeometricComparison assembled from the actual constructed
comparison, its geometric naturality and native weak admissibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.comparisonTarget_of_native_construction
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hCompletion : Completion.GeometricWeightInput.{0})
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0}) (hBettiComparison : Betti.ComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ :=
  A.comparisonTarget_of_native_integral_naturality hCohomology hCompletion hIntegralComparison hBettiComparison
    κ jComplex ι hplace ρ P ℓ hℓq A.constructedIntegralCrystallineEquiv_naturality

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
