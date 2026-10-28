import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterPurityTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LiftedRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate

/-! # Coefficient Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientPurity.Comparison

noncomputable section

/-! Full character purity gives the original CMExtraction conjugate-space
implications for the actual coefficient projectors and their Galois lifts. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ScalarConjugate.CM.Projectors
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LiftedRestriction.ParameterChoices

theorem coefficient_purity_hodge_types
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (L : IntermediateField ℚ ℂ) (hEL : E ≤ L) (hLalg : L ≤ HeckeCycles.Coefficients.CM.algebraicField)
    (v : Multiplicity.Odd.Sign E) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
    {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
    (κ : K →+* ParameterChoices.Qbar) (j : ParameterChoices.Qbar →+* ℂ)
    (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    {Hecke : Type} [CommRing Hecke] [Algebra ℚ Hecke]
    (ρ : A.HeckeRealization Hecke)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
      (A.complexFiber (j.comp κ)).scheme.hom)
    (χ : Hecke →ₐ[ℚ] ParameterChoices.Qbar) (initial : ℚ)
    (hpurity : NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity A κ j ρ P χ
      (fun τ => 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE τ)) : ℚ) * initial / 3))
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (e : ComplexMultiplication.WeightOne.CM.Complexification V ≃ₗ[ℂ] A.ComplexBetti (j.comp κ))
    (hF : H.holomorphic.map e.toLinearMap = A.bettiFiltration (j.comp κ) P 1)
    (p : L ⊗[ℚ] (V →ₗ[ℚ] V))
    (hne : ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V p ≠ 0)
    (σ : Gal(L/ℚ)) (τ : Gal(ParameterChoices.Qbar/ℚ))
    (hτ : ∀ a : L, j (τ ((HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm
      (IntermediateField.inclusion hLalg a))) = (σ a : ℂ))
    (hQ : ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V
      (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ L (V →ₗ[ℚ] V) σ p) ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H)
    (hRange : LinearMap.range (e.conj (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V
      (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ L (V →ₗ[ℚ] V) σ p))) =
      A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (τ (χ h)))) :
    let slope : ℚ := 1 / 2 -
      (ComplexMultiplication.SignSwitch.CM.signValue (v.val (HeckeCycles.Coefficients.CM.coefficientRestriction E L (HeckeCycles.Coefficients.CM.all_embeddings_in_field E L hEL) σ)) : ℚ) *
        initial / 3
    (slope = 1 → SameTestProjector.conjugateSpace L (LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L V V p)) σ ≤
      H.holomorphic) ∧
    (slope = 0 → SameTestProjector.conjugateSpace L (LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L V V p)) σ ≤
      H.antiholomorphic) := by
  let Q := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ L (V →ₗ[ℚ] V) σ p)
  have hr : LinearMap.range Q =
      SameTestProjector.conjugateSpace L (LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L V V p)) σ :=
    HeckeCycles.ScalarConjugate.CM.Projectors.conjugated_range_eq_conjugateSpace L p σ
  have hQne : Q ≠ 0 := by
    intro hz
    have hb : LinearMap.range Q = ⊥ := LinearMap.range_eq_bot.mpr hz
    exact HeckeCycles.ScalarConjugate.CM.Projectors.conjugateSpace_ne_bot L p σ hne (hr.symm.trans hb)
  have hs : A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (τ (χ h))) ≠ ⊥ := by
    intro hb
    have hz : e.conj Q = 0 := LinearMap.range_eq_bot.mp (hRange.trans hb)
    exact hQne ((e.conj).injective (by simpa only [map_zero] using hz))
  have hp := CharacterPurityTransport.Comparison.character_purity_hodge_types A κ j ρ P χ _ hpurity H e hF τ Q hQ hRange hs
  rw [LiftedRestriction.ParameterChoices.lifted_coefficient_restriction E L hEL hLalg j ιE hι σ τ hτ, hr] at hp
  exact hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientPurity.Comparison
