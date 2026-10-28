import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyRecovery

/-! # Picard Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.PicardPullback.Construction

noncomputable section

/-! An actual product-square line isomorphism gives the pullback
equation between the native homogeneous Picard-sheaf maps, before a
quotient dual is represented. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ A).left)
  (R : Picard.PoincareBundle.Line.Bundles.LineBundle (B ⊗ B).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ f).left).obj R.sheaf ≅ L.sheaf)
  (βL : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft A A))
    (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.Vertical.ProductParameters.inputRight A A))
    (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint A A)))
  (hβL : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βL))
  (βR : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber R (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβR : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βR))

include e in
theorem productNativeHomogeneousClass_pullback {T : Over S} (x : T ⟶ A) :
    (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f).app (op T)
      (SheafMap.Construction.productNativeHomogeneousClass R βR hβR (x ≫ f)) =
      SheafMap.Construction.productNativeHomogeneousClass L βL hβL x := by
  apply Subtype.ext
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 T ⊗ₘ f).left
    (Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv (T ⊗ B).left (Picard.PoincareBundle.Vertical.Homogeneity.familyClass R (x ≫ f))) =
    Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv (T ⊗ A).left (Picard.PoincareBundle.Vertical.Homogeneity.familyClass L x)
  exact (Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv_pullback (𝟙 T ⊗ₘ f).left
    (Picard.PoincareBundle.Vertical.Homogeneity.familyClass R (x ≫ f))).symm.trans
      (congrArg (Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv (T ⊗ A).left)
        (Picard.PoincareBundle.FamilyRecovery.Family.familyClass_recovery f f L R e x))

include e in
theorem productNativePicardSheafMap_pullback :
    uliftYoneda.map f ≫ SheafMap.Construction.productNativePicardSheafMap R βR hβR ≫
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom = SheafMap.Construction.productNativePicardSheafMap L βL hβL := by
  ext T x
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S)
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullbackPresheaf A B f)) T)
      (SheafMap.Construction.productNativeHomogeneousClass R βR hβR (x.down ≫ f))
  exact h.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app T)
    (productNativeHomogeneousClass_pullback f L R e βL hβL βR hβR x.down))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.PicardPullback.Construction
