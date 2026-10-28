import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.HeckeAction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ComplexBetti
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConjugateCharacterField

/-! # Hecke Coefficient Field -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Construct a finite local coefficient field for every conjugate character occurring in the fixed native complex Betti group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
  {H : Type} [CommRing H] [Algebra ℚ H]

def Geometry.AbelianH1Model.nativeHeckeCoefficientField (ρ : A.HeckeRealization H)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (hoccurs : A.bettiHeckeSummand j ρ (fun h => jComplex (χ h)) ≠ ⊥)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) :
    Linear.FiniteHeckeCoefficientField q (fun h => ι (σ (χ h))) := by
  letI : FiniteDimensional ℚ (A.Betti j) := A.rationalBetti_finiteDimensional j P
  have hsource : Linear.generalizedHeckeSummand
      (fun h => (A.bettiHecke j ρ h).baseChange ℂ) (fun h => jComplex (χ h)) ≠ ⊥ :=
    (HeckeSummandTransport.GeneralizedHecke.summand_ne_bot_iff (A.rationalComplexBettiEquiv j P) _ _
      (A.rationalComplexBettiEquiv_hecke j P ρ) _).mpr hoccurs
  have haction : Linear.generalizedHeckeSummand
      (fun h => (A.bettiHeckeAction j P ρ h).baseChange ℂ) (fun h => jComplex (χ h)) ≠ ⊥ := by
    simpa only [A.bettiHeckeAction_apply j P ρ] using hsource
  exact ConjugateCharacterField.finiteCoefficientFieldOfConjugateCharacter (A.bettiHeckeAction j P ρ) χ jComplex haction σ ι

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
