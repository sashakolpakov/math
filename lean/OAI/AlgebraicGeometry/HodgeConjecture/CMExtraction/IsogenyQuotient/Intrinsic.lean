import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualPoincare
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.BaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData

/-! # Intrinsic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Intrinsic

noncomputable section

/-! The native full IsogenyQuotient quotient supplies its actual TateComparison PEL isogeny
on the original fine model. Universal global functions are derived from
the full IsogenyQuotient witness, including for its pulled-back dual family;
no regularity assumption is added to the original correspondence cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N n : ℕ}
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}

variable (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
  (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions M.universal.polarized.abelian.scheme)
  (Q : Over M.space.left) (hQf : IsFinite Q.hom) (hQe : Etale Q.hom)

abbrev nativeFineCorrespondence
    (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (M.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q)) n M) :
    AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space where
  cover := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter M.space Q
  source := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q
  target := f.target
  finite := hQf
  etale := hQe

def nativeFineIsogeny
    (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (M.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q)) n M) :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny ((FineKernelData.fineFamily M).pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left)
      ((FineKernelData.fineFamily M).pullback f.target.left) n where
  isogeny := f.isogeny
  dualHom := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.isogeny.hom
    (M.universal.polarized.dual.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left)
    (M.universal.polarized.dual.pullback f.target.left)
  dualGroup := AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps.Construction.universalFunction_nativeDualMap_isMonHom f.isogeny.hom _ _
    ((AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source M.universal.polarized.polarization.isogeny.hom
      hA).pullback f.target.left)
  poincare := (AbelianScheme.IsogenyQuotient.UniversalFunction.DualPoincare.Construction.universalFunction_nativeDualMap_poincare _ _
    (hA.pullback
      (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left) f.isogeny.hom).symm
  equivariant a := by
    rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap, AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap]
    change (Over.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left).map
      (AbelianScheme.TateComparison.End.endSchemeMap M.universal.polarized.abelian.scheme (AbelianScheme.TateComparison.PELAdapters.actionToEnd M.universal.action a)) ≫ f.isogeny.hom =
        f.isogeny.hom ≫ (Over.pullback f.target.left).map
          (AbelianScheme.TateComparison.End.endSchemeMap M.universal.polarized.abelian.scheme (AbelianScheme.TateComparison.PELAdapters.actionToEnd M.universal.action a))
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]
    exact (f.action a).symm
  polarization := f.polarization
  marking := f.marking

theorem nativeFineIsogeny_hom
    (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (M.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q)) n M) :
    (nativeFineIsogeny M hA Q f).isogeny.hom = f.isogeny.hom := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Intrinsic
