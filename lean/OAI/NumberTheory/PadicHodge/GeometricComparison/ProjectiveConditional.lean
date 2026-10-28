import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveTarget
import OAI.NumberTheory.PadicHodge.GeometricComparison.CompletionIntrinsic
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.WeilPolynomial

/-! # Projective Conditional -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveConditional

noncomputable section

/-! The original comparison target from the actual projective complex
comparison and integral crystalline comparison. Only the still-needed
crystalline/étale characteristic-polynomial theorem is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem comparison_and_weak_admissibility_of_IntegralComparison
    (hIntegralComparison : Integral.Shared.CharpolyInput.{0})
    {K : Type} [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime]
    (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (jq : K →+* ℚ_[q])
    (hplace :
      (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (A : Geometry.AbelianH1Model K q jq)
    (H : Type) [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  obtain ⟨hC, W, hW, hCW⟩ := A.native_sharedPolynomial_of_IntegralComparison hIntegralComparison ℓ hℓq
  let : FiniteDimensional ℚ_[q] A.Crystalline := hC
  exact A.projective_comparisonTarget_of_shared_polynomial CompletionIntrinsic.nativeGeometricWeightInput
    κ jComplex ι hplace ρ P ℓ hℓq W hW hCW

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveConditional
