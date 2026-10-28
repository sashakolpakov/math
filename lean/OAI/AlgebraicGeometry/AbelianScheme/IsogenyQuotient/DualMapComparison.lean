import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.DualPoincareBundleRepresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback

/-! # Dual Map Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualMapComparison.Construction

noncomputable section

/-! The PoincareBundle dual morphism is the native HilbertConstruction Picard pullback morphism.
The comparison follows the actual line-class pullbacks through sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem e45HomogeneousPicardPresheafIso_pullback :
    Picard.PoincareBundle.Homogeneous.pullbackHomogeneousPresheaf f ≫ (HomogeneousPicardComparison.Construction.e45HomogeneousPicardPresheafIso A).hom =
      (HomogeneousPicardComparison.Construction.e45HomogeneousPicardPresheafIso B).hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousPresheaf f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  exact LineClassComparison.Construction.e45LineClassEquiv_pullback (Picard.PoincareBundle.Functor.familyMap f T.unop) q.val

theorem e45HomogeneousPicardSheafIso_pullback :
    Picard.PoincareBundle.Homogeneous.pullbackHomogeneousSheaf f ≫ (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A).hom =
      (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso B).hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf f := by
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (e45HomogeneousPicardPresheafIso_pullback f)).trans (F.map_comp _ _))

theorem e45HomogeneousPicardSheafIso_pullback_apply (T : Over S)
    (x : (Picard.PoincareBundle.Homogeneous.homogeneousSheaf B.scheme).obj.obj (.op T)) :
    (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A).hom.hom.app (.op T)
      ((Picard.PoincareBundle.Homogeneous.pullbackHomogeneousSheaf f).hom.app (.op T) x) =
    (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf f).hom.app (.op T)
      ((HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso B).hom.hom.app (.op T) x) :=
  congrArg (fun m => m.hom.app (.op T) x) (e45HomogeneousPicardSheafIso_pullback f)

theorem e45RepresentedDualMap_eq_native (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) :
    Picard.PoincareBundle.DualMaps.representedDualMap (Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation DA) (Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation DB) f =
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  apply FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_unique f DA DB
  intro T x
  have hr := Picard.PoincareBundle.DualMaps.representedDualMap_action
    (Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation DA) (Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation DB) f x
  have he := congrArg ((HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A).hom.hom.app (.op T)) hr
  rw [Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation_homEquiv] at he
  exact he.trans ((e45HomogeneousPicardSheafIso_pullback_apply f T _).trans
    (congrArg ((FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf f).hom.app (.op T))
      (Reference.DualPoincareBundleRepresentation.Construction.e45OriginalDualRepresentation_homEquiv DB x)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualMapComparison.Construction
