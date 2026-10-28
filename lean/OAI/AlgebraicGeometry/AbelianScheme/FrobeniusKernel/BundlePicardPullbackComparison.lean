import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback

/-! # Bundle Picard Pullback Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundlePicardPullbackComparison.Construction

noncomputable section

/-! Both Picard constructions pull back the same line bundles along the
same morphism. Their represented dual maps therefore agree exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousComparison OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]

theorem e45HomogeneousPresheafPullback_comparison :
    Picard.PoincareBundle.Homogeneous.pullbackHomogeneousPresheaf f ≫
        (Picard.PoincareBundle.HomogeneousComparison.homogeneousPresheafIso A).hom =
      (Picard.PoincareBundle.HomogeneousComparison.homogeneousPresheafIso B).hom ≫
        Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  exact Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv_pullback (T.unop ◁ f).left q.val

theorem e45HomogeneousSheafPullback_comparison :
    Picard.PoincareBundle.Homogeneous.pullbackHomogeneousSheaf f ≫
        (Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso A).hom =
      (Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso B).hom ≫
        Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f := by
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (e45HomogeneousPresheafPullback_comparison f)).trans (F.map_comp _ _))

theorem e45HomogeneousSheafPullback_section (T : Over S)
    (q : (Picard.PoincareBundle.Homogeneous.homogeneousSheaf B).obj.obj (op T)) :
    (Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op T)
        ((Picard.PoincareBundle.Homogeneous.pullbackHomogeneousSheaf f).hom.app (op T) q) =
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T)
        ((Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso B).hom.hom.app (op T) q) :=
  congrArg (fun t : Picard.PoincareBundle.Homogeneous.homogeneousSheaf B ⟶
      Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A => t.hom.app (op T) q)
    (e45HomogeneousSheafPullback_comparison f)

theorem e45RepresentedDualMap_eq_unbundled
    (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
    (DB : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) :
    Picard.PoincareBundle.DualMaps.representedDualMap (Picard.PoincareBundle.SharedRepresentation.representation DA)
        (Picard.PoincareBundle.SharedRepresentation.representation DB) f =
      Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback DA DB f := by
  apply DA.representable.homEquiv.injective
  calc
    _ = (Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op DB.abelian)
        ((Picard.PoincareBundle.SharedRepresentation.representation DA).homEquiv
          (Picard.PoincareBundle.DualMaps.representedDualMap
            (Picard.PoincareBundle.SharedRepresentation.representation DA)
            (Picard.PoincareBundle.SharedRepresentation.representation DB) f)) :=
      (Picard.PoincareBundle.SharedRepresentation.representation_action DA _).symm
    _ = (Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op DB.abelian)
        ((Picard.PoincareBundle.Homogeneous.pullbackHomogeneousSheaf f).hom.app (op DB.abelian)
          ((Picard.PoincareBundle.SharedRepresentation.representation DB).homEquiv (𝟙 DB.abelian))) :=
      congrArg ((Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op DB.abelian))
        ((Picard.PoincareBundle.SharedRepresentation.representation DA).homEquiv.apply_symm_apply _)
    _ = (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op DB.abelian)
        ((Picard.PoincareBundle.HomogeneousComparison.homogeneousSheafIso B).hom.hom.app (op DB.abelian)
          ((Picard.PoincareBundle.SharedRepresentation.representation DB).homEquiv (𝟙 DB.abelian))) :=
      e45HomogeneousSheafPullback_section f _ _
    _ = (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op DB.abelian)
        (DB.representable.homEquiv (𝟙 DB.abelian)) :=
      congrArg ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op DB.abelian))
        (Picard.PoincareBundle.SharedRepresentation.representation_action DB _)
    _ = _ := (DA.representable.homEquiv.apply_symm_apply _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundlePicardPullbackComparison.Construction
