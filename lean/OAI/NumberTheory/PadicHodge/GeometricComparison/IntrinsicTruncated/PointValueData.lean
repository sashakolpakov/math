import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftPointClass
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelTopCoverComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.RefinedTransferTrace

/-! # Point Value Data -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueData.AbelianModel

noncomputable section

/-! The two original point classes evaluated by the same bounded
crystalline global top-form map, before choosing local parameters. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem iso_hom_inv_apply {M N : AddCommGrpCat} (e : M ≅ N) (x : N) :
    e.hom (e.inv x) = x :=
  ConcreteCategory.congr_hom e.inv_hom_id x

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n : ℕ)

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedPointValueResolution := injectiveResolution
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := q)
    (J := Ideal.span {(q : WittVector q (ZMod q))})
    (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme) n)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedOrdinaryPointValue : A.NativeBoundedCrystallineCohomology n (A.dimension+A.dimension) :=
  (IntegralComparison.TruncatedModel.AdditiveGlobal.globalHomologyIso q (ZMod q) n (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedPointValueResolution n)
    (A.dimension+A.dimension)).hom
      (IntegralComparison.TruncatedModel.ModelTopCoverComparison.globalInput q (ZMod q) n (A.truncatedModel n).scheme
        A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedReductionSquare n)
        (A.truncatedPointValueResolution n) A.dimension
        (IntegralComparison.Intrinsic.TopFormTrace.cover (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))
        (IntegralComparison.Intrinsic.TopFormTrace.cover_top (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))
        (ULift.up.{2,1} (ULift.up.{1,0} (A.truncatedTracePointClass n))))

variable (m : ℕ) (hm : ¬q ∣ m)
local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.finiteMap : IsFinite (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_finite n m hm
local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.etaleMap : AlgebraicGeometry.Etale (A.truncatedShiftOver n m hm).left :=
  A.truncatedShiftMap_etale n m hm

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedFinitePointCover := IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover (TruncatedModel.NativeTruncatedBase.Ring q n)
  (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
  (IntegralComparison.Intrinsic.TopFormTrace.cover (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedFinitePointCover_top : iSup (A.truncatedFinitePointCover n m hm) = ⊤ :=
  IntegralComparison.Intrinsic.RefinedTransferTrace.inverseCover_top (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    (IntegralComparison.Intrinsic.TopFormTrace.cover (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))
    (IntegralComparison.Intrinsic.TopFormTrace.cover_top (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedFiniteTracePointClass :
    IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite.cohomology (A.truncatedModel n).scheme
      (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedTraceMorphism n) A.dimension :=
  (IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso (A.truncatedModel n).scheme
    (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedTraceMorphism n) A.dimension).inv (A.truncatedShiftSerrePointClass n m hm)

section
attribute [local irreducible] HomologicalComplex.homology
attribute [local irreducible] IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedFiniteTracePointClass_serre :
    (IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso (A.truncatedModel n).scheme
      (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedTraceMorphism n) A.dimension).hom (A.truncatedFiniteTracePointClass n m hm) =
      A.truncatedShiftSerrePointClass n m hm := by
  have h := iso_hom_inv_apply (IntegralComparison.Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso (A.truncatedModel n).scheme
    (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedTraceMorphism n) A.dimension) (A.truncatedShiftSerrePointClass n m hm)
  convert h using 1
  as_aux_lemma => rfl

end

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.truncatedFinitePointValue : A.NativeBoundedCrystallineCohomology n (A.dimension+A.dimension) :=
  (IntegralComparison.TruncatedModel.AdditiveGlobal.globalHomologyIso q (ZMod q) n (A.truncatedShiftModel n m hm)
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedPointValueResolution n)
    (A.dimension+A.dimension)).hom
      (IntegralComparison.TruncatedModel.ModelTopCoverComparison.globalInput q (ZMod q) n (A.truncatedShiftModel n m hm)
        A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedShiftModel_square n m hm)
        (A.truncatedPointValueResolution n) A.dimension
        (A.truncatedFinitePointCover n m hm) (A.truncatedFinitePointCover_top n m hm)
        (ULift.up.{2,1} (ULift.up.{1,0} (A.truncatedFiniteTracePointClass n m hm))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueData.AbelianModel
