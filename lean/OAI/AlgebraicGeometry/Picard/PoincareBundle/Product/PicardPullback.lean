import OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyRecovery

/-! # Picard Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PicardPullback

noncomputable section

/-! The actual line recovery becomes the represented Picard pullback equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

variable {S : Scheme.{u}} {A B X Y DX DY : Over S} [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)
  (βL : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (Vertical.ProductParameters.inputLeft A X)) (Line.Fibers.fiber L (Vertical.ProductParameters.inputRight A X))
    (Line.Fibers.fiber L (Vertical.ProductParameters.outputPoint A X))) (hβL : IsIso (Bilinear.BilinearPullback.toHom βL))
  (βR : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber R (Vertical.ProductParameters.inputLeft B Y)) (Line.Fibers.fiber R (Vertical.ProductParameters.inputRight B Y))
    (Line.Fibers.fiber R (Vertical.ProductParameters.outputPoint B Y))) (hβR : IsIso (Bilinear.BilinearPullback.toHom βR))

include e

/-- The line recovery identifies the actual homogeneous presheaf fibers. -/
theorem homogeneousClass_recovery {T : Over S} (x : T ⟶ A) :
    (Homogeneous.pullbackHomogeneousPresheaf g).app (op T) (Map.homogeneousClass R βR hβR (x ≫ f)) =
      Map.homogeneousClass L βL hβL x := by
  apply Subtype.ext
  exact FamilyRecovery.Family.familyClass_recovery f g L R e x

/-- Sheafification carries the same actual recovery to the homogeneous Picard sections. -/
theorem sectionClass_recovery {T : Over S} (x : T ⟶ A) :
    (Homogeneous.pullbackHomogeneousSheaf g).hom.app (op T) (Map.sectionClass R βR hβR (x ≫ f)) =
      Map.sectionClass L βL hβL x := by
  have h := congrArg (fun b => b.app (op T) (Map.homogeneousClass R βR hβR (x ≫ f)))
    (toSheafify_naturality (Scheme.fppfTopology.over S) (Homogeneous.pullbackHomogeneousPresheaf g))
  exact h.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf X)).app (op T))
    (homogeneousClass_recovery f g L R e βL hβL βR hβR x))

/-- Product-line recovery implies the actual represented pullback identity. -/
theorem representedMap_pullback
    (HX : (Homogeneous.homogeneousSheaf X).obj.RepresentableBy DX)
    (HY : (Homogeneous.homogeneousSheaf Y).obj.RepresentableBy DY) :
    f ≫ Map.representedMap R βR hβR HY ≫ DualMaps.representedDualMap HX HY g = Map.representedMap L βL hβL HX := by
  apply HX.homEquiv.injective
  rw [← Category.assoc, DualMaps.representedDualMap_action, Map.representedMap_action]
  have hs := sectionClass_recovery f g L R e βL hβL βR hβR (𝟙 A)
  rw [Category.id_comp] at hs
  exact hs.trans (Equiv.apply_symm_apply _ _).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PicardPullback
