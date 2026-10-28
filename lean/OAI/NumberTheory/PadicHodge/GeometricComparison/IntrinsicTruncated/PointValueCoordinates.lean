import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverPositiveValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveRefinementRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceTopRefinementData

/-! # Point Value Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The point-value cover coordinates recover the actual ordinary
small point class and the original common-cover finite point class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq) (n : ℕ)

local instance Geometry.AbelianH1Model.ordinary_forms_qc :
    (Integral.FormsModules.IntegralFormsModules.sheaf (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme
      A.dimension).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme A.dimension

theorem Geometry.AbelianH1Model.truncatedOrdinaryPointValue_coordinates (hpos : 0 < A.dimension) :
    (IntegralComparison.TruncatedModel.TopCoverPositiveValue.smallCoordinates q (ZMod q) n
      (A.truncatedModel n).scheme A.dimension hpos (A.truncatedTraceCover n)
      (A.truncatedTraceCover_top n) (A.truncatedTraceCover_affine n)).hom
      (A.truncatedTracePointClass n) = A.truncatedSmallPointClass n hpos := by
  have h := IntegralComparison.ModuleCech.PositiveRefinementRecovery.reverse_hom (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedTraceCover n) (A.truncatedSmallCover n)
    (A.truncatedTraceCover_top n) (A.truncatedSmallCover_top n)
    (A.truncatedTraceCover_affine n) (A.truncatedSmallCover_affine n)
    (Integral.FormsModules.IntegralFormsModules.sheaf (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme A.dimension)
    A.dimension hpos
  exact ConcreteCategory.congr_hom h (A.truncatedTracePointClass n)

variable (m : ℕ) (hm : ¬q ∣ m)

theorem Geometry.AbelianH1Model.truncatedFinitePointCover_affine (j : ULift (Fin (A.truncatedTraceDimension n+2))) :
    IsAffineOpen (A.truncatedFinitePointCover n m hm j) :=
  IntegralComparison.Intrinsic.RefinedTransferTrace.inverseCover_affine (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    (IntegralComparison.Intrinsic.TopFormTrace.cover (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))
    (IntegralComparison.Intrinsic.TopFormTrace.cover_affine (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)) j

local instance Geometry.AbelianH1Model.finite_forms_qc :
    (Integral.FormsModules.IntegralFormsModules.sheaf (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm)
      A.dimension).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) A.dimension

def Geometry.AbelianH1Model.truncatedFiniteSmallPointClass (hpos : 0 < A.dimension) :=
  (IntegralComparison.TruncatedModel.TopCoverPositiveValue.smallCoordinates q (ZMod q) n
    (A.truncatedShiftModel n m hm) A.dimension hpos (A.truncatedFinitePointCover n m hm)
    (A.truncatedFinitePointCover_top n m hm) (A.truncatedFinitePointCover_affine n m hm)).hom
    (A.truncatedFiniteTracePointClass n m hm)

theorem Geometry.AbelianH1Model.truncatedFiniteSmallPointClass_common (hpos : 0 < A.dimension) :
    IntegralComparison.TruncatedModel.SourceTopRefinementData.Morphism.topMap q (ZMod q) n (A.truncatedShiftOver n m hm)
      A.dimension (A.truncatedFiniteSmallPointClass n m hm hpos) =
    A.truncatedShiftPointClass n m hm hpos := by
  have hcycle := IntegralComparison.ModuleCech.PositiveRefinementRecovery.cycle_apply (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm)
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm))
    (IntegralComparison.TruncatedModel.MorphismTopEdgeBase.sourceCover q (ZMod q) n (A.truncatedShiftOver n m hm))
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm))
    (A.truncatedShiftCommonCover_top n m hm)
    (fun j => (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) j).property)
    (A.truncatedShiftCommonCover_affine n m hm)
    (Integral.FormsModules.IntegralFormsModules.sheaf (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) A.dimension)
    A.dimension hpos (A.truncatedFinitePointCover n m hm)
    (A.truncatedFinitePointCover_top n m hm) (A.truncatedFinitePointCover_affine n m hm)
    (IntegralComparison.TruncatedModel.MorphismSourceRefinementCoordinates.openRefinement q (ZMod q) n
      (A.truncatedShiftOver n m hm)) (A.truncatedFiniteTracePointClass n m hm)
  have h := congrArg (IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso (A.truncatedModel n).scheme
    (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm) (A.truncatedTraceMorphism n)
    A.dimension).hom hcycle
  have hc : (A.truncatedShiftCommonSerreIso n m hm hpos).hom
      (IntegralComparison.TruncatedModel.SourceTopRefinementData.Morphism.topMap q (ZMod q) n
        (A.truncatedShiftOver n m hm) A.dimension (A.truncatedFiniteSmallPointClass n m hm hpos)) =
      A.truncatedShiftSerrePointClass n m hm := by
    apply Eq.trans _ (A.truncatedFiniteTracePointClass_serre n m hm)
    convert h using 1
    as_aux_lemma => rfl
  apply (A.truncatedShiftCommonSerreIso n m hm hpos).addCommGroupIsoToAddEquiv.injective
  exact hc.trans (A.truncatedShiftPointClass_serre n m hm hpos).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
