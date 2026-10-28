import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingProjectors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters

/-! # Commuting Comparison Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingComparisonProjectors.Spectral

noncomputable section

/-! Retain Hecke commutation in the same comparison projectors, with
characters and every coefficient-conjugate range in the fixed closure. -/

open scoped TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projectors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

theorem construct_commuting_comparison_projectors
    (E : IntermediateField ℚ ℂ) [NumberField E]
    {U H Φ : Type*} [AddCommGroup U] [Module ℚ U] [CommRing H] [Algebra ℚ H]
    (W : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (T : H →ₐ[ℚ] Module.End ℚ U)
    (hHodge : ∀ h, ComplexMultiplication.WeightOne.CM.IsHodgeMap W W (T h)) (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification U)
    (j : AlgebraicClosure ℚ →+* ℂ) :
    ∃ K : IntermediateField ℚ ℂ, NumberField K ∧ IsGalois ℚ K ∧ E ≤ K ∧
      ∃ (hKalg : K ≤ HeckeCycles.Coefficients.CM.algebraicField) (n : ℕ) (p : Fin n → K ⊗[ℚ] (U →ₗ[ℚ] U))
        (χ : Fin n → H →ₐ[ℚ] AlgebraicClosure ℚ),
        let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (p i)
        let A := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K U U (p i))
        (∀ i, (P i).comp (P i) = P i) ∧
        (∀ i, LinearMap.range (P i) = Definitions.CM.conjugateSpace K (A i) 1) ∧
        (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace W W) ∧
        (∀ i h, Commute (P i) ((T h).baseChange ℂ)) ∧
        (∀ i, ∃ φ, P i (theta φ) ≠ 0) ∧
        (∀ φ, ∑ i, P i (theta φ) = theta φ) ∧
        (∀ i, LinearMap.range (P i) = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ)
          (fun h => j (χ i h))) ∧
        (∀ i (σ : Gal(K/ℚ)),
          let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U
            (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] U) σ (p i))
          ∃ τ : Gal(AlgebraicClosure ℚ/ℚ),
            (∀ a : K, j (τ ((HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm
              (IntermediateField.inclusion hKalg a))) = (σ a : ℂ)) ∧
            Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace W W ∧
            LinearMap.range Pσ = HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ)
              (fun h => j (τ (χ i h)))) := by
  let : FiniteDimensional ℚ U := W.finiteDimensional
  obtain ⟨K, hK, hGal, hEK, hKalg, n, p, ψ, hid, hr, hh, hPc, hocc, hsum, hψ, hconj⟩ :=
    CommutingProjectors.Spectral.construct_commuting_algebraic_projectors E W T
      (fun a b => (Commute.all a b).map T) hHodge theta
  have hne : ∀ i, HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) (fun h => (ψ i h : ℂ)) ≠ ⊥ := by
    intro i hz
    obtain ⟨φ, hφ⟩ := hocc i
    have hp : ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K U U (p i) = 0 :=
      LinearMap.range_eq_bot.mp ((hψ i).trans hz)
    exact hφ (LinearMap.congr_fun hp (theta φ))
  let χ : Fin n → H →ₐ[ℚ] AlgebraicClosure ℚ :=
    fun i => HeckeCycles.ChosenCharacters.CM.chosenCharacter j T (fun h => (ψ i h : ℂ)) (hne i)
  refine ⟨K, hK, hGal, hEK, hKalg, n, p, χ, hid, hr, hh, hPc, hocc, hsum, ?_, ?_⟩
  · intro i
    simpa only [χ, HeckeCycles.ChosenCharacters.CM.chosenCharacter_apply] using hψ i
  · intro i σ
    obtain ⟨τ, hτ, hH, hR⟩ := hconj i σ
    refine ⟨HeckeCycles.ChosenCharacters.CM.chosenAutomorphism j τ, ?_, hH, ?_⟩
    · intro a
      rw [HeckeCycles.ChosenCharacters.CM.chosenAutomorphism_apply, (HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).apply_symm_apply]
      exact hτ a
    · simpa only [χ, HeckeCycles.ChosenCharacters.CM.chosenAutomorphism_character] using hR

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingComparisonProjectors.Spectral
