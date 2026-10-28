import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardMapBaseChange

/-! # Canonical Dual Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualBaseChange

noncomputable section

/-! Base change of the canonical dual map, using only Picard functor
compatibility and the actual representing equivalences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback

variable {S T : Scheme.{0}} {g h : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : T ⟶ S) (p : A.scheme ⟶ B.scheme) [IsMonHom p]

theorem canonicalHomogeneousPullback_baseChange (U : Over T)
    (z : (B.pullback f).homogeneousPicardSheaf.obj.obj (op U)) :
    A.homogeneousPicardBaseChangeEquiv f U
        ((AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p)).hom.app (op U) z) =
      (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf p).hom.app (op ((Over.map f).obj U))
        (B.homogeneousPicardBaseChangeEquiv f U z) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun r => r.hom) (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf_baseChange f p)) (op U)) z

theorem canonicalDual_baseChange (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B) :
    (Over.pullback f).map (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap p DA DB) =
      AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p) (DA.pullback f) (DB.pullback f) := by
  apply AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_unique (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap f p) (DA.pullback f) (DB.pullback f)
  intro U x
  apply (A.homogeneousPicardBaseChangeEquiv f U).injective
  exact (DA.pullbackRepresentable_comparison f U _).trans
    ((congrArg DA.representable.homEquiv
      (HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap p DA DB) f U x)).trans
      ((AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_action p DA DB (DB.abelian.baseChangePointsEquiv f U x)).trans
        ((congrArg ((AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf p).hom.app (op ((Over.map f).obj U)))
          (DB.pullbackRepresentable_comparison f U x).symm).trans
            (canonicalHomogeneousPullback_baseChange f p U _).symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualBaseChange
