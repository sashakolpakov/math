import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Correspondence
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedFiberProjections
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionChosenKernels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceTransport

/-! # Chosen Kernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenKernels.IsogenyQuotient

noncomputable section

section

/-! The retained IntegralModel family identifies the chosen kernels of each
retained branch with those of its corresponding original fine-model branch. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N q : ℕ} [Fact q.Prime]
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
  {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N} (I : RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic.IntegralModel P iota κ M)

def retainedPointFineIso {T : Over (Spec (.of I.base.extension.carrier))}
    (x : T ⟶ IsogenyQuotient.Correspondence.retainedSpace I) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((IsogenyQuotient.Correspondence.retainedFamily I).pullback x.left)
      ((IsogenyQuotient.FineKernelData.fineFamily M).pullback (ReducedCorrespondence.IsogenyQuotient.originalModelPoint I.base.fieldExtension M.space I.spread.genericIso x).left) :=
  PEL.RestrictionChosenKernels.IsogenyQuotient.restrictionPointFamilyIso (IsogenyQuotient.Correspondence.retainedFamily I) (IsogenyQuotient.FineKernelData.fineFamily M)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap I.base.fieldExtension M.space I.spread.genericIso) (IsogenyQuotient.Correspondence.retainedFamilyIso I)
    x.left _ (ReducedFiberProjections.IsogenyQuotient.originalModelPoint_left I.base.fieldExtension M.space I.spread.genericIso x)

variable (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space) (t : AbelianScheme.TateComparison.Local.IntegralType s)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (f : IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M C t)

def retainedChosenKernel (v : Fin s) :
    AbelianScheme.TateComparison.Subgroups.PointSubgroup ((IsogenyQuotient.Correspondence.retainedFamily I).pullback (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).source.left).abelian :=
  (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (IsogenyQuotient.Correspondence.retainedUniversalIsogeny I C t f).isogeny.hom).inf
    (AbelianScheme.TateComparison.Subgroups.splitBlock ((IsogenyQuotient.Correspondence.retainedFamily I).pullback (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).source.left)
      (χ (v, false)) t.multiplierNat)

def retainedChosenKernelAtLift {T : Over (Spec (.of I.base.extension.carrier))}
    (x : T ⟶ IsogenyQuotient.Correspondence.retainedSpace I) (c : T ⟶ (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).cover)
    (w : c ≫ (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).source = x) (v : Fin s) :
    AbelianScheme.TateComparison.Subgroups.PointSubgroup ((IsogenyQuotient.Correspondence.retainedFamily I).pullback x.left).abelian :=
  ((retainedChosenKernel I C t χ f v).pullback c.left).comapHom
    (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso (IsogenyQuotient.Correspondence.retainedFamily I).abelian c.left (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).source.left
      x.left (congrArg (fun z => z.left) w)).hom

theorem retained_chosen_kernel_at_branch {T : Over (Spec (.of I.base.extension.carrier))}
    (x : T ⟶ IsogenyQuotient.Correspondence.retainedSpace I) (z : (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).Fiber x) (v : Fin s) :
    retainedChosenKernelAtLift I C t χ f x z.val z.property v =
      (IsogenyQuotient.FineKernelData.chosenKernelAtLift M C t χ f
        (ReducedCorrespondence.IsogenyQuotient.originalModelPoint I.base.fieldExtension M.space I.spread.genericIso x)
        (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv I.base.fieldExtension M.space I.spread.genericIso C x z).val
        (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv I.base.fieldExtension M.space I.spread.genericIso C x z).property v).comapHom
          (retainedPointFineIso I x).abelian.hom := by
  exact PEL.RestrictionChosenKernels.IsogenyQuotient.restrictPELIsogeny_chosen_at_lift (IsogenyQuotient.Correspondence.retainedFamily I) (IsogenyQuotient.FineKernelData.fineFamily M)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap I.base.fieldExtension M.space I.spread.genericIso) (IsogenyQuotient.Correspondence.retainedFamilyIso I)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap I.base.fieldExtension M.space I.spread.genericIso C)
    C.source.left C.target.left (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).source.left
    (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).target.left
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source I.base.fieldExtension M.space I.spread.genericIso C)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_target I.base.fieldExtension M.space I.spread.genericIso C)
    f (χ (v, false)) t.multiplierNat z.val.left x.left
    (congrArg (fun z => z.left) z.property) _ _
    (ReducedFiberProjections.IsogenyQuotient.modelFiberEquiv_left I.base.fieldExtension M.space I.spread.genericIso C x z)
    (ReducedFiberProjections.IsogenyQuotient.originalModelPoint_left I.base.fieldExtension M.space I.spread.genericIso x)
    (congrArg (fun z => z.left)
      (ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv I.base.fieldExtension M.space I.spread.genericIso C x z).property)

end

/-! The universal chosen-kernel classification transfers through the
actual retained IntegralModel family and the exact correspondence fiber equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N q : ℕ} [Fact q.Prime]
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
  {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N} (I : RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic.IntegralModel P iota κ M)
  (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space) (t : AbelianScheme.TateComparison.Local.IntegralType s)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (f : IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M C t)

theorem retained_kernel_geometry (hf : IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M C t χ f) (v : Fin s) :
    (retainedChosenKernel I C t χ f v).HasFiniteEtaleModel ∧
      (retainedChosenKernel I C t χ f v).HasGeometricType q (t.exponentNat v) :=
  PEL.RestrictionKernel.IsogenyQuotient.restrictPELIsogeny_splitKernel_geometry (IsogenyQuotient.Correspondence.retainedFamily I) (IsogenyQuotient.FineKernelData.fineFamily M)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap I.base.fieldExtension M.space I.spread.genericIso) (IsogenyQuotient.Correspondence.retainedFamilyIso I)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap I.base.fieldExtension M.space I.spread.genericIso C)
    C.source.left C.target.left (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).source.left
    (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).target.left
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source I.base.fieldExtension M.space I.spread.genericIso C)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_target I.base.fieldExtension M.space I.spread.genericIso C)
    f (χ (v, false)) t.multiplierNat (t.exponentNat v) (hf.1 v).1 (hf.1 v).2

theorem retained_kernel_classification (hf : IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M C t χ f)
    (T : Over (Spec (.of I.base.extension.carrier))) (x : T ⟶ IsogenyQuotient.Correspondence.retainedSpace I)
    (F : AbelianScheme.TateComparison.Subgroups.KernelChoices ((IsogenyQuotient.Correspondence.retainedFamily I).pullback x.left) (fun v => χ (v, false))
      t.multiplierNat t.exponentNat) :
    ∃! c : T ⟶ (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).cover,
      ∃ w : c ≫ (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).source = x,
        ∀ v, retainedChosenKernelAtLift I C t χ f x c w v = F.val v := by
  let ep := retainedPointFineIso I x
  let ek := HeckeCycles.KernelChoiceTransport.CM.choiceEquiv ep (fun v => χ (v, false))
    t.multiplierNat t.exponentNat
  let eb := ReducedCorrespondence.IsogenyQuotient.modelFiberEquiv I.base.fieldExtension M.space I.spread.genericIso C x
  obtain ⟨b, ⟨hb, hk⟩, huniq⟩ := hf.2 _ _ (ek F)
  let z := eb.symm ⟨b, hb⟩
  have hval (v : Fin s) :
      IsogenyQuotient.FineKernelData.chosenKernelAtLift M C t χ f
        (ReducedCorrespondence.IsogenyQuotient.originalModelPoint I.base.fieldExtension M.space I.spread.genericIso x)
        (eb z).val (eb z).property v = (ek F).val v := by
    change IsogenyQuotient.FineKernelData.chosenKernelAtLift M C t χ f _ (eb (eb.symm ⟨b, hb⟩)).val
      (eb (eb.symm ⟨b, hb⟩)).property v = _
    simpa only [Equiv.apply_symm_apply] using hk v
  have hret (v : Fin s) : retainedChosenKernelAtLift I C t χ f x z.val z.property v = F.val v := by
    rw [retained_chosen_kernel_at_branch, hval]
    exact congrArg (fun G => G.val v) (ek.symm_apply_apply F)
  refine ⟨z.val, ⟨z.property, hret⟩, ?_⟩
  rintro d ⟨hd, hkd⟩
  let zd : (IsogenyQuotient.Correspondence.retainedFineCorrespondence I C).Fiber x := ⟨d, hd⟩
  have hdval : (eb zd).val = b := by
    apply huniq
    refine ⟨(eb zd).property, ?_⟩
    intro v
    have hh := (retained_chosen_kernel_at_branch I C t χ f x zd v).symm.trans (hkd v)
    have hh' := congrArg (fun H => H.comapHom ep.abelian.inv) hh
    exact (SubgroupPullbackCoherence.IsogenyQuotient.subgroup_comap_iso_inverse _ ep.symm.abelian).symm.trans hh'
  have he : eb zd = eb z := by
    apply Subtype.ext
    exact hdval.trans (congrArg Subtype.val (eb.apply_symm_apply ⟨b, hb⟩)).symm
  exact congrArg Subtype.val (eb.injective he)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenKernels.IsogenyQuotient
