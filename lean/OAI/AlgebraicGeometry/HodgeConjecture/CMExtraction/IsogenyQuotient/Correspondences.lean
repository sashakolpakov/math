import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.IntrinsicClassification
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Realization
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Labels
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.MultisetTransport

/-! # Correspondences -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Correspondences.Intrinsic

noncomputable section

/-! Specialize full native IsogenyQuotient to the same previously retained moduli
model, prime, and q-adic choice. Preserve every original fiber witness
and the complete raw-Hecke multiset after transport to the retained model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Matrix BigOperators

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  {q : ℕ} [Fact q.Prime] (hgood : PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (hFiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0})

local instance fullIsogenyQuotient_retained_level_neZero : NeZero M.level :=
  ⟨(lt_of_lt_of_le (by decide : 0 < 3) M.level_ge_three).ne'⟩

def RetainedNativeFullWitnesses (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.model.space) : Prop :=
  ∀ t, ∃ hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions M.model.universal.polarized.abelian.scheme,
    ∃ (Q : Over M.model.space.left) (hQf : IsFinite Q.hom) (hQe : Etale Q.hom)
    (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (M.model.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.model.space Q))
      (q ^ t.multiplierNat) M.model),
    C t = Intrinsic.nativeFineCorrespondence M.model Q hQf hQe f ∧
    TransportWitness.TransportIntegralFiberWitness M.model M.fine hA j
      (algebraMap E M.integral.base.extension.carrier)
      (hgood.split_coordinates _ _ _ j) hs hdegree t.multiplierNat
      (Labels.retainedIsogenyQuotientLabels E P hP hμ) (Labels.retainedIsogenyQuotientLabels_swap E P hP hμ)
      t.exponentNat t.exponentNat_le (FineProjectors.integralType_exponentNat_antitone t)
      hgood.level_coprime hgood.polarization_coprime hFiniteDescent Q f

def RetainedFullRawMultisets (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.model.space) : Prop :=
  ∀ (t : AbelianScheme.TateComparison.Local.IntegralType s) (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of M.integral.base.extension.carrier))
    (x : Over.mk c ⟶ Correspondence.retainedSpace M.integral),
    ∃ hfin : Finite ((Correspondence.retainedFineCorrespondence M.integral (C t)).Fiber x),
      @AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset _ _ hfin (fun z : (Correspondence.retainedFineCorrespondence M.integral (C t)).Fiber x =>
        ReducedCorrespondence.IsogenyQuotient.originalModelPoint M.integral.base.fieldExtension M.model.space M.integral.spread.genericIso
          ((Correspondence.retainedFineCorrespondence M.integral (C t)).endpoint z)) =
      AbelianScheme.IsogenyQuotient.Reference.HeckeTargets.Construction.originalRawHeckeMultiset M.model M.fine j (algebraMap E M.integral.base.extension.carrier)
        (hgood.split_coordinates _ _ _ j) hs hdegree t.multiplierNat
        (Labels.retainedIsogenyQuotientLabels E P hP hμ) (Labels.retainedIsogenyQuotientLabels_swap E P hP hμ)
        t.exponentNat t.exponentNat_le (FineProjectors.integralType_exponentNat_antitone t)
        hgood.level_coprime hgood.polarization_coprime hFiniteDescent
        (ReducedCorrespondence.IsogenyQuotient.originalModelPoint M.integral.base.fieldExtension M.model.space M.integral.spread.genericIso x)

theorem fullIsogenyQuotient_retained_correspondences (hIsogenyQuotient : Transport.CompleteIsogenyQuotientTransportInput) :
    ∃ C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.model.space,
      RetainedNativeFullWitnesses E P hP hμ v hv W R M hs hdegree hgood j hFiniteDescent C ∧
      RetainedFullRawMultisets E P hP hμ v hv W R M hs hdegree hgood j hFiniteDescent C ∧
      (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j
        (fun t => Correspondence.retainedFineCorrespondence M.integral (C t))).RealizesIsogenyQuotient := by
  have hχ (w : Fin s) : HeckeModel.Intrinsic.retainedLocalCharacter E P hP hμ v hv W R M j (w, false) =
      j.localCharacter (algebraMap E M.integral.base.extension.carrier)
        (Labels.retainedIsogenyQuotientLabels E P hP hμ (.inl w)) := by
    rfl
  have hf (t : AbelianScheme.TateComparison.Local.IntegralType s) := IntrinsicClassification.native_family_classifies M.model M.fine
    j (algebraMap E M.integral.base.extension.carrier) (hgood.split_coordinates _ _ _ j)
    hs hdegree (Labels.retainedIsogenyQuotientLabels E P hP hμ) (Labels.retainedIsogenyQuotientLabels_swap E P hP hμ)
    hgood.level_coprime hgood.polarization_coprime hFiniteDescent t
    (HeckeModel.Intrinsic.retainedLocalCharacter E P hP hμ v hv W R M j) hχ
    (hIsogenyQuotient s hs hdegree P hP (RingHom.id E) E.val.toRingHom
      (by simpa only [RingHom.comp_id] using hμ.symm) M.level M.deep M.model M.fine
      M.ballComponents q j (algebraMap E M.integral.base.extension.carrier)
      (hgood.split_coordinates _ _ _ j) t.multiplierNat
      (Labels.retainedIsogenyQuotientLabels E P hP hμ) (Labels.retainedIsogenyQuotientLabels_swap E P hP hμ)
      t.exponentNat t.exponentNat_le (FineProjectors.integralType_exponentNat_antitone t)
      hgood.level_coprime hgood.polarization_coprime hFiniteDescent)
  choose hA Q hQf hQe f hclass hwitness hraw using hf
  let C := fun t => Intrinsic.nativeFineCorrespondence M.model (Q t) (hQf t) (hQe t) (f t)
  refine ⟨C, ?_, ?_, ?_⟩
  · intro t
    exact ⟨hA t, Q t, hQf t, hQe t, f t, rfl, hwitness t⟩
  · intro t c x
    obtain ⟨hfin, hr⟩ := hraw t (c ≫ M.integral.base.fieldExtension)
      (ReducedCorrespondence.IsogenyQuotient.originalModelPoint M.integral.base.fieldExtension M.model.space M.integral.spread.genericIso x)
    let : Finite ((C t).Fiber
      (ReducedCorrespondence.IsogenyQuotient.originalModelPoint M.integral.base.fieldExtension M.model.space M.integral.spread.genericIso x)) := hfin
    let hret : Finite ((Correspondence.retainedFineCorrespondence M.integral (C t)).Fiber x) :=
      Finite.of_equiv _ (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv M.integral.base.fieldExtension M.model.space
        M.integral.spread.genericIso (C t) x).symm
    exact ⟨hret, MultisetTransport.model_raw_multiset M.integral.base.fieldExtension M.model.space
      M.integral.spread.genericIso (C t) x _ hr⟩
  · exact Realization.retained_realizes M.integral C (HeckeModel.Intrinsic.retainedLocalCharacter E P hP hμ v hv W R M j)
      (fun t => Intrinsic.nativeFineIsogeny M.model (hA t) (Q t) (f t)) hclass

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Correspondences.Intrinsic
