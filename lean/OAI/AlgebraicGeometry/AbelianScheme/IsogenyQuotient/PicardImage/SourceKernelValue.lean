import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceMap
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup

/-! # Source Kernel Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceKernelValue.Construction

noncomputable section

/-! A point in the actual source-map kernel gives zero relative
Picard pullback, through the native source-dual representation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)

theorem picardImageSourceKernel_relative_zero {T : Over S} (x : T ⟶ C)
    (hx : x ≫ SourceMap.Construction.picardImageSourceMap D f i = 1) :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) (i.app (op T) (ULift.up x))) =
        AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  have hp : (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T) (i.app (op T) (ULift.up x)) =
      Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A T := by
    rw [← SourceMap.Construction.picardImageSourceMap_value, hx, D.origin]
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun a => a.hom) (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback_inclusion A B f)) (op T))
    (i.app (op T) (ULift.up x))
  change (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T)
      ((Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom.app (op T) (i.app (op T) (ULift.up x))) = _ at hc
  rw [hp, Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one] at hc
  exact hc.symm.trans ((Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply A T 1).symm.trans
    ((Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom A T).map_one.trans (Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one A T).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceKernelValue.Construction
