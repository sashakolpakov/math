import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientIntrinsicArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceGeometricFrame
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicTransition

/-! # Coefficient Source Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSourceFrame.CM

noncomputable section

/-! The source frame for explicit multiplicity coefficients has a
constant invertible comparison with the native geometric frame. All
required period positivity is supplied by the actual coefficient signs. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (a : Fin 2 → K) (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)
  (s : Fin 2 → Fin places.count → Bool) (hμ : ∀ j, s j places.distinguished = true)
  (hs : ∀ j τ, if s j τ = true then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a j)).im < 0
    else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a j)).im)

def sourceCoefficientComplexComponents : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ]
    (Fin places.count → ((Fin 3 × Fin 2 → ℂ) × (Fin 3 × Fin 2 → ℂ))) :=
  (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (CoefficientIntrinsicArithmetic.CM.sourceCoefficientArithmetic K B places δ hδ hδ0 a ha ha0 s hμ hs)).comp
    (SourceComponents.CM.sourcePairedTensorCoordinates K places)

theorem source_coefficient_components_eq_pair (Q : Lagrangians.CM.LagrangianPair K B places s)
    (hδQ : Q.delta = δ) (haQ : Q.a = a) :
    sourceCoefficientComplexComponents K B places δ hδ hδ0 a ha ha0 s hμ hs =
      SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place := by
  subst δ
  subst a
  rfl

omit s hμ hs in
theorem exists_source_coefficient_frame (d : Fin 2 → Gal(K/ℚ) → Bool)
    (hμ : ∀ j, d j (places.representative places.distinguished) = true)
    (hs : ∀ j τ, if d j (places.representative τ) = true then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a j)).im < 0
      else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a j)).im) :
    ∃ C : (PeriodTotal.CM.TotalPositions K places → ℂ) ≃ₗ[ℂ] (Fin places.count × (Fin 3 × Fin 2) → ℂ),
      ∀ (z : B.Domain) (u : PeriodTotal.CM.TotalPositions K places → ℂ),
        sourceCoefficientComplexComponents K B places δ hδ hδ0 a ha ha0
          (fun j τ => d j (places.representative τ)) hμ hs
          (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u) =
        RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (CoefficientIntrinsicArithmetic.CM.sourceCoefficientArithmetic K B places δ hδ hδ0 a ha ha0
          (fun j τ => d j (places.representative τ)) hμ hs) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (C u) := by
  have hs' : ∀ j τ, if τ = places.distinguished ∨ d j (places.representative τ) = true
      then (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a j)).im < 0
      else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (δ * a j)).im := by
    intro j τ
    by_cases he : τ = places.distinguished
    · subst τ
      simpa only [hμ, or_true, ite_true] using hs j places.distinguished
    · simpa only [he, false_or] using hs j τ
  have hex := CoefficientPeriods.CM.exists_lagrangian_pair_with_coefficients K B places
    (fun j τ => d j (places.representative τ)) δ a hδ0 hδ ha0 ha hs'
  let Q := hex.choose
  have hc := source_coefficient_components_eq_pair K B places δ hδ hδ0 a ha ha0
    (fun j τ => d j (places.representative τ)) hμ hs Q hex.choose_spec.1 hex.choose_spec.2
  refine ⟨SourceIntrinsicTransition.CM.directSourceFrameCoefficientEquiv K Q, ?_⟩
  intro z u
  have he := congrArg (fun C : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ]
      (Fin places.count → ((Fin 3 × Fin 2 → ℂ) × (Fin 3 × Fin 2 → ℂ))) =>
    C (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u)) hc
  exact he.trans (SourceGeometricFrame.CM.direct_source_geometric_frame K d Q hμ B.other_place z u)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSourceFrame.CM
