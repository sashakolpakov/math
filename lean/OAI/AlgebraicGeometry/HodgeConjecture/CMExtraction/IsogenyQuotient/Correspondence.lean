import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondenceSquares
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.RestrictionKernel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData
import OAI.RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily

/-! # Correspondence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Correspondence

noncomputable section

/-! Construct the IsogenyQuotient correspondence and universal PEL isogeny on the
identical retained IntegralModel integral spread. The base field extension, generic
isomorphism, and polarized universal family are those already stored in I. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ} {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N}
  (I : RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic.IntegralModel P iota κ M)

abbrev retainedSpace := (Over.pullback I.base.generic).obj I.spread.toOver

instance retainedSpace_smooth : Smooth (retainedSpace I).hom := by
  let : Smooth I.spread.toOver.hom := I.smooth
  change Smooth (pullback.snd I.spread.toOver.hom I.base.generic)
  infer_instance

instance retainedSpace_noetherian : IsLocallyNoetherian (retainedSpace I).left :=
  LocallyOfFiniteType.isLocallyNoetherian (retainedSpace I).hom

instance retainedSpace_reduced : IsReduced (retainedSpace I).left :=
  Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (retainedSpace I).hom

abbrev retainedFineCorrespondence (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space) :
    AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence (retainedSpace I) :=
  ReducedCorrespondence.IsogenyQuotient.modelCorrespondence I.base.fieldExtension M.space I.spread.genericIso C

abbrev retainedFamily : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N
    (retainedSpace I).left :=
  (HeckeCycles.PELFamily.CM.Family.ofActionData I.spread.universal.data).pullback
    (pullback.fst I.spread.toOver.hom I.base.generic)

def retainedFamilyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (retainedFamily I)
      ((FineKernelData.fineFamily M).pullback (ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap I.base.fieldExtension M.space I.spread.genericIso)) := by
  rw [ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap_eq]
  exact HeckeCycles.PELFamily.CM.Isomorphisms.toFamilyIso I.spread.familyIso

def retainedUniversalIsogeny {q : ℕ} [Fact q.Prime]
    (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space) (t : AbelianScheme.TateComparison.Local.IntegralType s)
    (f : FineKernelData.UniversalIsogeny (q := q) M C t) :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny ((retainedFamily I).pullback (retainedFineCorrespondence I C).source.left)
      ((retainedFamily I).pullback (retainedFineCorrespondence I C).target.left)
      (q ^ t.multiplierNat) :=
  PEL.PELRestriction.IsogenyQuotient.restrictPELIsogeny (retainedFamily I) (FineKernelData.fineFamily M)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap I.base.fieldExtension M.space I.spread.genericIso) (retainedFamilyIso I)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap I.base.fieldExtension M.space I.spread.genericIso C)
    C.source.left C.target.left (retainedFineCorrespondence I C).source.left
    (retainedFineCorrespondence I C).target.left
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_source I.base.fieldExtension M.space I.spread.genericIso C)
    (ReducedCorrespondenceSquares.IsogenyQuotient.originalCoverMap_target I.base.fieldExtension M.space I.spread.genericIso C) f

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Correspondence
