import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CofinalModuli

/-! # Initial Cofinal Moduli -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialCofinalModuli.Intrinsic

noncomputable section

/-! Fix the source reference and normalized test once, then construct
the required integral model at every sufficiently divisible level. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem exists_initial_cofinal_moduli
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E) (hCongruenceLevel : HeckeCycles.ReferenceDatum.CM.CongruenceLevelInput E places.count)
    (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement)
    (hReferenceFamily : AbelianScheme.IsogenyQuotient.Reference.Family.Construction.ReferenceFamilyInput) (hIntegralModel : RepresentationTheory.Hecke.IntegralModel.OrdinaryCharacterIntrinsic.FullIntegralModelInput)
    (dref : Fin places.count → Bool) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin places.count × Fin 3) MpR MpF MpA)
    (base : ℕ) (hbase : 0 < base) :
    ∃ (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count)
      (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom),
      P.b = B.b ∧ P.distinguished.val = 0 ∧
      (∀ i, P.embeddings i = HeckeCycles.ReferenceDatum.CM.embeddings E places (InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places i)) ∧
      P.compactSigns = dref ∘ InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places ∧
      ∃ R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W,
        ∃ N : ℕ, 3 ≤ N ∧ base ∣ N ∧ R.depth ∣ N ∧
          ∀ L : ℕ, 0 < L → N ∣ L →
            ∃ M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R, M.level = L := by
  obtain ⟨P, hP, hμ, hb, hz, he, hd, ⟨R⟩⟩ :=
    InitialTest.Intrinsic.exists_initial_retained_test E B places hCongruenceLevel hAdelicTheta dref v hv W
  refine ⟨P, hP, hμ, hb, hz, he, hd, R, ?_⟩
  exact CofinalModuli.Intrinsic.exists_retained_cofinal_moduli E P hP hμ v hv W R hReferenceFamily hIntegralModel
    (HeckeCycles.ReferenceDatum.CM.source_degree E places).1 (HeckeCycles.ReferenceDatum.CM.source_degree E places).2 base hbase

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialCofinalModuli.Intrinsic
