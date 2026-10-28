import OAI.NumberTheory.PadicHodge.GeometricComparison.CharacterKernel
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CharacterField

/-! # Conjugate Character Field -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConjugateCharacterField

noncomputable section

/-! Every algebraic conjugate of a character occurring in finite rational cohomology has a finite local coefficient field. -/

open scoped TensorProduct

variable {q : ℕ} [Fact q.Prime]
  {H V : Type*} [CommRing H] [Algebra ℚ H]
  [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

def finiteCoefficientFieldOfConjugateCharacter
    (ρ : H →ₐ[ℚ] Module.End ℚ V) (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (j : AlgebraicClosure ℚ →+* ℂ)
    (hS : Linear.generalizedHeckeSummand (fun h => (ρ h).baseChange ℂ) (fun h => j (χ h)) ≠ ⊥)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) :
    Linear.FiniteHeckeCoefficientField q (fun h => ι (σ (χ h))) := by
  letI : FiniteDimensional ℚ χ.toLinearMap.range :=
    CharacterKernel.GeneralizedHecke.finite_character_range_of_summand ρ χ j.toRatAlgHom hS
  exact Finite.CharacterField.finiteCoefficientFieldOfRationalCharacter χ (ι.comp σ.toRingHom)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConjugateCharacterField
