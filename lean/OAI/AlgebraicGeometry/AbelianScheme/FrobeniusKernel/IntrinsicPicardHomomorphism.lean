import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedGroups

/-! # Intrinsic Picard Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPicardHomomorphism.Construction.IntrinsicPicard

noncomputable section

/-! Actual Picard pullback is a group homomorphism for the native
Picard-derived dual groups, directly from pullback of tensor products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} (A B : Over S) [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]

def homogeneousPullbackGroupPresheaf :
    Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B ⟶ Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A where
  app T := CommGrpCat.ofHom {
    toFun := (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).app T
    map_one' := Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (T.unop ◁ f).left)
    map_mul' x y := Subtype.ext (Picard.Homomorphisms.SchemePullback.Construction.pullbackClass_mul (T.unop ◁ f).left x.val y.val) }
  naturality {T U} t := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).naturality_apply t x

def homogeneousPullbackHom (T : Over S) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (.op T) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (.op T) :=
  Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyMapHom (homogeneousPullbackGroupPresheaf A B f) (.op T)

theorem homogeneousPullbackHom_apply (T : Over S)
    (x : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (.op T)) :
    homogeneousPullbackHom A B f T x = (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (.op T) x :=
  Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyMapHom_apply (homogeneousPullbackGroupPresheaf A B f) (.op T) x

variable {A B} (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (E : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)

def dualPullbackPoints (T : Over S) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup E
    (T ⟶ E.abelian) →* (T ⟶ D.abelian) :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup E
  (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D T).symm.toMonoidHom.comp
    ((homogeneousPullbackHom A B f T).comp (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv E T).toMonoidHom)

theorem dualPullbackPoints_apply (T : Over S) (x : T ⟶ E.abelian) :
    dualPullbackPoints f D E T x = x ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup E
  apply (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D T).injective
  change Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D T ((Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv D T).symm
      (homogeneousPullbackHom A B f T (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv E T x))) = _
  rw [MulEquiv.apply_symm_apply, homogeneousPullbackHom_apply,
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv_apply, Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv_apply]
  exact (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback_representation D E f x).symm

theorem dualPullback_isMonHom :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup E
    IsMonHom (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup E
  apply RepresentedGroups.Construction.isMonHom_of_point_operations (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f)
  · intro T
    exact (dualPullbackPoints_apply f D E T 1).symm.trans (dualPullbackPoints f D E T).map_one
  · intro T x y
    exact (dualPullbackPoints_apply f D E T (x * y)).symm.trans
      (((dualPullbackPoints f D E T).map_mul x y).trans
        (congrArg₂ (· * ·) (dualPullbackPoints_apply f D E T x) (dualPullbackPoints_apply f D E T y)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPicardHomomorphism.Construction.IntrinsicPicard
