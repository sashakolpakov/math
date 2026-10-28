import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Transport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Intrinsic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineClassification
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineProjectors
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.KernelBlocks
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.TransportWitness

/-! # Intrinsic Classification -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.IntrinsicClassification

noncomputable section

/-! The complete native IsogenyQuotient proposition supplies a single original
fine-model correspondence with its full PEL target, chosen-kernel
classification, and full raw-Hecke multiset identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [Field L] [NumberField L]
  {s N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (aE : E →+* L)
  (hsplit : j.HasSplitCoordinates aE) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
  (hFiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0}) (t : AbelianScheme.TateComparison.Local.IntegralType s)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (hχ : ∀ v, χ (v, false) = j.localCharacter aE (labels (.inl v)))

include hχ in
theorem native_family_classifies
    (hfull : ∃ hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions M.universal.polarized.abelian.scheme,
      ∃ (Q : Over M.space.left) (_hQf : IsFinite Q.hom) (_hQe : Etale Q.hom)
      (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (M.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q))
        (q ^ t.multiplierNat) M),
      TransportWitness.TransportIntegralFiberWitness M hM hA j aE hsplit hs hdegree t.multiplierNat labels hlabels
        t.exponentNat t.exponentNat_le (FineProjectors.integralType_exponentNat_antitone t) hcop hpol hFiniteDescent Q f) :
    ∃ hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions M.universal.polarized.abelian.scheme,
    ∃ (Q : Over M.space.left) (hQf : IsFinite Q.hom) (hQe : Etale Q.hom)
      (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (M.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q))
        (q ^ t.multiplierNat) M),
      FineKernelData.ClassifiesChosenKernels M (Intrinsic.nativeFineCorrespondence M Q hQf hQe f) t χ
        (Intrinsic.nativeFineIsogeny M hA Q f) ∧
      TransportWitness.TransportIntegralFiberWitness M hM hA j aE hsplit hs hdegree t.multiplierNat labels hlabels
        t.exponentNat t.exponentNat_le (FineProjectors.integralType_exponentNat_antitone t) hcop hpol hFiniteDescent Q f ∧
      ∀ (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : Over.mk c ⟶ M.space),
        ∃ hfin : Finite (AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q) x),
          @AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.correspondenceFiberMultiset _ _ _ _ _ (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q) f.target x hfin =
            AbelianScheme.IsogenyQuotient.Reference.HeckeTargets.Construction.originalRawHeckeMultiset M hM j aE hsplit hs hdegree t.multiplierNat labels hlabels
              t.exponentNat t.exponentNat_le (FineProjectors.integralType_exponentNat_antitone t) hcop hpol hFiniteDescent x := by
  let : ∀ v, Module (ZMod (q ^ t.multiplierNat)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (t.exponentNat v)) :=
    fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q t.multiplierNat (t.exponentNat v) (t.exponentNat_le v)
  obtain ⟨hA, Q, hQf, hQe, f, hwitness⟩ := hfull
  have hw := hwitness
  unfold TransportWitness.TransportIntegralFiberWitness at hw
  rw [← FineProjectors.fineFamily_action M] at hw
  dsimp only [TransportWitness.TransportIntegralFiberWitnessAtAction] at hw
  obtain ⟨repr, _e, _he, _hsf, _hse, model, hker, _hisotropic, hraw⟩ := hw
  refine ⟨hA, Q, hQf, hQe, f, ?_, hwitness, hraw⟩
  apply FineClassification.represented_isogeny_classifies M j aE hsplit (fun v => labels (.inl v)) t Q repr
    f.target hQf hQe (Intrinsic.nativeFineIsogeny M hA Q f) χ hχ
  intro v
  unfold FineKernelData.chosenKernel
  rw [hχ v]
  exact KernelBlocks.fullKernel_chosen_block j aE hsplit (FineKernelData.fineFamily M) M.space.hom Q
    t.multiplierNat labels t.exponentNat _ _ model f.isogeny hker v

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.IntrinsicClassification
