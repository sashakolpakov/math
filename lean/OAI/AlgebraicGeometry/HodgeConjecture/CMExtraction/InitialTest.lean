import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialReference
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison

/-! # Initial Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialTest.Intrinsic

noncomputable section

/-! Starting from the source ball, choose the active-first reference and
one normalized theta test before every level and prime choice. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison.Multiplicity

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem exists_initial_retained_test
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E) (hCongruenceLevel : HeckeCycles.ReferenceDatum.CM.CongruenceLevelInput E places.count)
    (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement)
    (dref : Fin places.count → Bool) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin places.count × Fin 3) MpR MpF MpA) :
    ∃ (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count)
      (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom),
      P.b = B.b ∧ P.distinguished.val = 0 ∧
      (∀ i, P.embeddings i = HeckeCycles.ReferenceDatum.CM.embeddings E places (InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places i)) ∧
      P.compactSigns = dref ∘ InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places ∧
      Nonempty (PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W) := by
  obtain ⟨P, hP, hμ, hb, hz, he, hd⟩ := InitialReference.Intrinsic.initial_reference_with_active_zero E B places hCongruenceLevel dref
  exact ⟨P, hP, hμ, hb, hz, he, hd, PreprimeComparison.Intrinsic.exists_retained_preprime_data E P hP hμ v hv W
    (InitialReference.Intrinsic.source_places_at_least_two E B places) hAdelicTheta⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialTest.Intrinsic
