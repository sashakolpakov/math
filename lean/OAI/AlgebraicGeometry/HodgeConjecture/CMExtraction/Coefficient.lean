import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientPurity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarTrace

/-! # Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Coefficient.Comparison

noncomputable section

/-! Apply the unchanged five-clause extraction to the actual coefficient
projectors, using full ExtremeSlopes character purity and proved scalar trace descent. -/

open scoped TensorProduct Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

theorem extraction_from_character_purity
    (E L : IntermediateField ℚ ℂ)
    [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [NumberField L] [IsGalois ℚ L]
    (hEL : E ≤ L) (hLalg : L ≤ HeckeCycles.Coefficients.CM.algebraicField)
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
    {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
    (κ : K →+* ParameterChoices.Qbar) (j : ParameterChoices.Qbar →+* ℂ)
    (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    {Hecke : Type} [CommRing Hecke] [Algebra ℚ Hecke]
    (ρ : A.HeckeRealization Hecke)
    (proj : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
      (A.complexFiber (j.comp κ)).scheme.hom)
    (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (e : ComplexMultiplication.WeightOne.CM.Complexification V ≃ₗ[ℂ] A.ComplexBetti (j.comp κ))
    (hF : H.holomorphic.map e.toLinearMap = A.bettiFiltration (j.comp κ) proj 1)
    (I Φ : Type*) [Fintype I]
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification V)
    (p : I → L ⊗[ℚ] (V →ₗ[ℚ] V))
    (χ : I → Hecke →ₐ[ℚ] ParameterChoices.Qbar) (initial : I → ℚ)
    (hextreme : ∀ i, initial i = -3 / 2 ∨ initial i = 3 / 2)
    (hpurity : ∀ i, NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity A κ j ρ proj (χ i)
      (fun τ => 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE τ)) : ℚ) * initial i / 3))
    (hid : ∀ i, (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i)).comp
      (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i)) = ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i))
    (hHodge : ∀ i, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i) ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H)
    (htheta : ∀ f, theta f ∈ H.holomorphic)
    (hoccurs : ∀ i, ∃ f, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i) (theta f) ≠ 0)
    (hsum : ∀ f, ∑ i, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i) (theta f) = theta f)
    (hconj : ∀ i (σ : Gal(L/ℚ)),
      let Q := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ L (V →ₗ[ℚ] V) σ (p i))
      ∃ τ : Gal(ParameterChoices.Qbar/ℚ),
        (∀ a : L, j (τ ((HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm
          (IntermediateField.inclusion hLalg a))) = (σ a : ℂ)) ∧
        Q ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H ∧
        LinearMap.range (e.conj Q) = A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (τ (χ i h))))
    (B : Type*) [AddCommGroup B] [Module ℚ B]
    (HB : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure B)
    (restrict : V →ₗ[ℚ] B) (hrestrict : ComplexMultiplication.WeightOne.CM.IsHodgeMap H HB restrict) :
    let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i)
    let C := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L V V (p i))
    let res := HeckeCycles.Coefficients.CM.coefficientRestriction E L (HeckeCycles.Coefficients.CM.all_embeddings_in_field E L hEL)
    (∀ i, initial i = -3 / 2) ∧
    (∀ i σ,
      (v.val (res σ) = true → SameTestProjector.conjugateSpace L (C i) σ ≤ H.holomorphic) ∧
      (v.val (res σ) = false → SameTestProjector.conjugateSpace L (C i) σ ≤ H.antiholomorphic)) ∧
    (∀ i (x : L ⊗[ℚ] V), x ∈ C i →
      ∃ f : ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V,
        f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H ∧
        ∀ τ : Gal(E/ℚ), f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) =
          if τ = 1 then ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion L V x else 0) ∧
    (∀ i, LinearMap.range (P i) ≤ SameTestProjector.cmIdSpan E v H) ∧
    (∀ f, restrict.baseChange ℂ (theta f) ∈ SameTestProjector.cmIdSpan E v HB) := by
  let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p i)
  let C := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L V V (p i))
  let hL := HeckeCycles.Coefficients.CM.all_embeddings_in_field E L hEL
  apply SameTestProjector.cm_extraction_from_galois_conjugate_hodge_signs E L v hv hL
    (HeckeCycles.Coefficients.CM.coefficientRestriction E L hL) (HeckeCycles.Coefficients.CM.coefficientRestriction_spec E L hL)
    V H (ScalarTrace.scalarTraceInput_of_numberField L (E →ₗ[ℚ] V)) I Φ theta P C
    hid (fun i => HeckeCycles.Coefficients.CM.extended_range_eq_conjugateSpace L (p i))
    hHodge htheta hoccurs hsum initial hextreme ?_ B HB restrict hrestrict
  intro i σ
  obtain ⟨τ, hτ, hQ, hRange⟩ := hconj i σ
  have hne : P i ≠ 0 := by
    obtain ⟨f, hf⟩ := hoccurs i
    intro hz
    exact hf (by change P i (theta f) = 0; rw [hz]; rfl)
  exact CoefficientPurity.Comparison.coefficient_purity_hodge_types E L hEL hLalg v ιE A κ j hι ρ proj (χ i)
    (initial i) (hpurity i) H e hF (p i) hne σ τ hτ hQ hRange

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Coefficient.Comparison
