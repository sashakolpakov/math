import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ProjectorTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonProjectors

/-! # Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Projectors.CM

noncomputable section

/-! Construct the finite active coefficient projectors of the original
Albanese Hecke realization. The same algebraic characters identify their
actual GeometricComparison Betti ranges, including every scalar conjugate. -/

open scoped TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ProjectorTransport.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) (j : K →+* ℂ)
  (E : IntermediateField ℚ ℂ) [NumberField E]
  {H Φ : Type} [CommRing H] [Algebra ℚ H]
  (ρ : A.HeckeRealization H) (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j))
  (jComplex : AlgebraicClosure ℚ →+* ℂ)

def Conclusion : Prop :=
  ∃ L : IntermediateField ℚ ℂ, NumberField L ∧ IsGalois ℚ L ∧ E ≤ L ∧
    ∃ (hLalg : L ≤ Coefficients.CM.algebraicField) (n : ℕ)
      (p : Fin n → L ⊗[ℚ] (A.Betti j →ₗ[ℚ] A.Betti j))
      (χ : Fin n → H →ₐ[ℚ] AlgebraicClosure ℚ),
      let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L (A.Betti j) (A.Betti j) (p i)
      let B := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L (A.Betti j) (A.Betti j) (p i))
      (∀ i, (P i).comp (P i) = P i) ∧
      (∀ i, LinearMap.range (P i) = CMExtraction.Definitions.CM.conjugateSpace L (B i) 1) ∧
      (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (Comap.CM.hodge A j) (Comap.CM.hodge A j)) ∧
      (∀ i, ∃ φ, P i (theta φ) ≠ 0) ∧
      (∀ φ, ∑ i, P i (theta φ) = theta φ) ∧
      (∀ i, LinearMap.range (Intrinsic.ProjectorTransport.CM.projector A j (P i)) =
        A.bettiHeckeSummand j ρ (fun h => jComplex (χ i h))) ∧
      (∀ i, A.bettiHeckeSummand j ρ (fun h => jComplex (χ i h)) ≠ ⊥) ∧
      (∀ i (σ : Gal(L/ℚ)),
        let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L (A.Betti j) (A.Betti j)
          (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ L (A.Betti j →ₗ[ℚ] A.Betti j) σ (p i))
        ∃ τ : Gal(AlgebraicClosure ℚ/ℚ),
          (∀ a : L, jComplex (τ ((ChosenCharacters.CM.chosenClosureEquiv jComplex).symm
            (IntermediateField.inclusion hLalg a))) = (σ a : ℂ)) ∧
          Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (Comap.CM.hodge A j) (Comap.CM.hodge A j) ∧
          LinearMap.range Pσ = CMExtraction.Definitions.CM.conjugateSpace L (B i) σ ∧
          LinearMap.range (Intrinsic.ProjectorTransport.CM.projector A j Pσ) =
            A.bettiHeckeSummand j ρ (fun h => jComplex (τ (χ i h))))

theorem active_projectors : Conclusion A j E ρ theta jComplex := by
  obtain ⟨L, hL, hGal, hEL, hLalg, n, p, χ, hid, hr, hh, hocc, hsum, hχ, hconj⟩ :=
    ComparisonProjectors.CM.construct_comparison_projectors E (Comap.CM.hodge A j)
      (Comap.CM.heckeAction A j ρ) (Comap.CM.heckeAction_hodge A j ρ) theta jComplex
  have hnative (i : Fin n) := Intrinsic.ProjectorTransport.CM.range_of_character A j ρ _ _ (hχ i)
  refine ⟨L, hL, hGal, hEL, hLalg, n, p, χ, hid, hr, hh, hocc, hsum, hnative, ?_, ?_⟩
  · intro i
    rw [← hnative i]
    obtain ⟨φ, hφ⟩ := hocc i
    exact Intrinsic.ProjectorTransport.CM.range_nonzero A j _ (theta φ) hφ
  · intro i σ
    obtain ⟨τ, hτ, hH, hspace⟩ := hconj i σ
    exact ⟨τ, hτ, hH,
      ScalarConjugate.CM.Projectors.conjugated_range_eq_conjugateSpace L (p i) σ,
      Intrinsic.ProjectorTransport.CM.range_of_character A j ρ _ _ hspace⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Projectors.CM
