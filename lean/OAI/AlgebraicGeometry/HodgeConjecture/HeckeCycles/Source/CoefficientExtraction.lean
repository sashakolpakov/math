import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedLevelExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LiftedRestriction

/-! # Coefficient Extraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoefficientExtraction.CM

noncomputable section

/-! Apply the full named CMExtraction specification to the actual coefficient
projectors, using their proved Hodge signs for algebraic-closure lifts.
The source predicate is not strengthened by this endpoint theorem. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LiftedRestriction.ParameterChoices

universe uV uI uPhi

theorem extraction
    (E F : IntermediateField ℚ ℂ)
    [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [NumberField F] [IsGalois ℚ F]
    (hEF : E ≤ F) (hFalg : F ≤ Coefficients.CM.algebraicField)
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (j : CMExtraction.ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    {V : Type uV} [AddCommGroup V] [Module ℚ V] (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    {I : Type uI} [Fintype I] {Φ : Type uPhi}
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification V) (p : I → F ⊗[ℚ] (V →ₗ[ℚ] V))
    (hid : ∀ i, (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (p i)).comp
      (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (p i)) = ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (p i))
    (hHodge : ∀ i, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (p i) ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H)
    (htheta : ∀ φ, theta φ ∈ H.holomorphic)
    (hoccurs : ∀ i, ∃ φ, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (p i) (theta φ) ≠ 0)
    (hsum : ∀ φ, ∑ i, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (p i) (theta φ) = theta φ)
    (hconj : ∀ i (σ : Gal(F/ℚ)),
      let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F (V →ₗ[ℚ] V) σ (p i))
      ∃ τ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ),
        (∀ a : F, j (τ ((ChosenCharacters.CM.chosenClosureEquiv j).symm
          (IntermediateField.inclusion hFalg a))) = (σ a : ℂ)) ∧
        (v.val (CMExtraction.ParameterChoices.restriction E ιE τ) = true → LinearMap.range Pσ ≤ H.holomorphic) ∧
        (v.val (CMExtraction.ParameterChoices.restriction E ιE τ) = false → LinearMap.range Pσ ≤ H.antiholomorphic))
    (hCMExtraction : MatchedLevelExtraction.CM.Construction.CMExtractionInput.{uV, uI, uPhi, uV}) :
    ∀ φ, theta φ ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v H := by
  let hF := Coefficients.CM.all_embeddings_in_field E F hEF
  let res := Coefficients.CM.coefficientRestriction E F hF
  let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients F V V (p i)
  let A := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange F V V (p i))
  have htypes : ∀ i σ,
      (v.val (res σ) = true → CMExtraction.Definitions.CM.conjugateSpace F (A i) σ ≤ H.holomorphic) ∧
      (v.val (res σ) = false → CMExtraction.Definitions.CM.conjugateSpace F (A i) σ ≤ H.antiholomorphic) := by
    intro i σ
    obtain ⟨τ, hτ, hh, ha⟩ := hconj i σ
    have hr := ScalarConjugate.CM.Projectors.conjugated_range_eq_conjugateSpace F (p i) σ
    have he := CMExtraction.LiftedRestriction.ParameterChoices.lifted_coefficient_restriction E F hEF hFalg j ιE hι σ τ hτ
    rw [he, hr] at hh ha
    exact ⟨hh, ha⟩
  have h := MatchedLevelExtraction.CM.Construction.extraction_at_matched_level E F v hv hF res
    (Coefficients.CM.coefficientRestriction_spec E F hF) V H I Φ theta P A hid
    (fun i => Coefficients.CM.extended_range_eq_conjugateSpace F (p i)) hHodge htheta hoccurs hsum
    (fun _ => (-3 / 2 : ℚ)) (fun _ => Or.inl rfl) (by
      intro i σ
      have ht := htypes i σ
      cases hs : v.val (res σ) <;> norm_num [ComplexMultiplication.SignSwitch.CM.signValue, hs] at ht ⊢ <;> exact ht)
    V H LinearMap.id (ComplexMultiplication.WeightOne.CM.isHodgeMap_id H) hCMExtraction
  intro φ
  simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using h φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoefficientExtraction.CM
