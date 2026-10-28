import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projectors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters

/-! # Comparison Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonProjectors.CM

noncomputable section

/-! The projectors constructed from a rational Hecke action have algebraic
characters in GeometricComparison's chosen algebraic closure. Every coefficient-conjugate
projector is the actual summand for a matching conjugated character. -/

open scoped TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projectors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

theorem construct_comparison_projectors
    (E : IntermediateField ℚ ℂ) [NumberField E]
    {U H Φ : Type*} [AddCommGroup U] [Module ℚ U] [CommRing H] [Algebra ℚ H]
    (W : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (T : H →ₐ[ℚ] Module.End ℚ U)
    (hHodge : ∀ h, ComplexMultiplication.WeightOne.CM.IsHodgeMap W W (T h)) (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification U)
    (j : AlgebraicClosure ℚ →+* ℂ) :
    ∃ K : IntermediateField ℚ ℂ, NumberField K ∧ IsGalois ℚ K ∧ E ≤ K ∧
      ∃ (hKalg : K ≤ Coefficients.CM.algebraicField) (n : ℕ) (p : Fin n → K ⊗[ℚ] (U →ₗ[ℚ] U))
        (χ : Fin n → H →ₐ[ℚ] AlgebraicClosure ℚ),
        let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (p i)
        let A := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U (p i))
        (∀ i, (P i).comp (P i) = P i) ∧
        (∀ i, LinearMap.range (P i) = CMExtraction.Definitions.CM.conjugateSpace K (A i) 1) ∧
        (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace W W) ∧
        (∀ i, ∃ φ, P i (theta φ) ≠ 0) ∧
        (∀ φ, ∑ i, P i (theta φ) = theta φ) ∧
        (∀ i, LinearMap.range (P i) = HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ)
          (fun h => j (χ i h))) ∧
        (∀ i (σ : Gal(K/ℚ)),
          let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U
            (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ (p i))
          ∃ τ : Gal(AlgebraicClosure ℚ/ℚ),
            (∀ a : K, j (τ ((ChosenCharacters.CM.chosenClosureEquiv j).symm
              (IntermediateField.inclusion hKalg a))) = (σ a : ℂ)) ∧
            Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace W W ∧
            LinearMap.range Pσ = HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ)
              (fun h => j (τ (χ i h)))) := by
  let : FiniteDimensional ℚ U := W.finiteDimensional
  obtain ⟨K, hK, hGal, hEK, hKalg, n, p, ψ, hid, hr, hh, hocc, hsum, hψ, hconj⟩ :=
    Projectors.CM.construct_algebraic_active_projectors_with_characters E W T
      (fun a b => (Commute.all a b).map T) hHodge theta
  have hne : ∀ i, HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) (fun h => (ψ i h : ℂ)) ≠ ⊥ := by
    intro i hz
    obtain ⟨φ, hφ⟩ := hocc i
    have hp : ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (p i) = 0 :=
      LinearMap.range_eq_bot.mp ((hψ i).trans hz)
    exact hφ (LinearMap.congr_fun hp (theta φ))
  let χ : Fin n → H →ₐ[ℚ] AlgebraicClosure ℚ :=
    fun i => ChosenCharacters.CM.chosenCharacter j T (fun h => (ψ i h : ℂ)) (hne i)
  refine ⟨K, hK, hGal, hEK, hKalg, n, p, χ, hid, hr, hh, hocc, hsum, ?_, ?_⟩
  · intro i
    simpa only [χ, ChosenCharacters.CM.chosenCharacter_apply] using hψ i
  · intro i σ
    obtain ⟨τ, hτ, hH, hR⟩ := hconj i σ
    refine ⟨ChosenCharacters.CM.chosenAutomorphism j τ, ?_, hH, ?_⟩
    · intro a
      rw [ChosenCharacters.CM.chosenAutomorphism_apply, (ChosenCharacters.CM.chosenClosureEquiv j).apply_symm_apply]
      exact hτ a
    · simpa only [χ, ChosenCharacters.CM.chosenAutomorphism_character] using hR

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonProjectors.CM
