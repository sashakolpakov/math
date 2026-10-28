import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup

/-! # Unbundled Picard Pullback Hom -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnbundledPicardPullbackHom.Construction

noncomputable section

/-! Actual line-bundle pullback preserves the intrinsic commutative
group laws of the dimension-independent Picard sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]

def nativeHomogeneousPicardPullbackGroupPresheaf :
    Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B ⟶
      Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf A where
  app T := CommGrpCat.ofHom {
    toFun := (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).app T
    map_one' := Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (T.unop ◁ f).left)
    map_mul' x y := Subtype.ext (Picard.Homomorphisms.SchemePullback.Construction.pullbackClass_mul (T.unop ◁ f).left x.val y.val) }
  naturality := by
    intro T U a
    ext x
    exact (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).naturality_apply a x

def nativeHomogeneousPicardPullbackHom (T : Over S) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T) →*
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (op T) :=
  Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyMapHom (nativeHomogeneousPicardPullbackGroupPresheaf f) (op T)

theorem nativeHomogeneousPicardPullbackHom_apply (T : Over S)
    (x : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T)) :
    nativeHomogeneousPicardPullbackHom f T x =
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T) x :=
  Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyMapHom_apply (nativeHomogeneousPicardPullbackGroupPresheaf f) (op T) x

theorem nativeHomogeneousPicardPullback_kernel_relative (T : Over S)
    (x : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hx : (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T) x = 1) :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) x) =
        AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  have h := congrArg (fun p : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A =>
    p.hom.app (op T) x) (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback_inclusion A B f)
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T)
    ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T) x) = _ at h
  rw [hx] at h
  exact h.symm.trans (by
    rw [← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply, map_one]
    exact (Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one A T).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnbundledPicardPullbackHom.Construction
