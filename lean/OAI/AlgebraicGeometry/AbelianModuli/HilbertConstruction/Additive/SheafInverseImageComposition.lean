import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.SheafInverseImage

/-! # Sheaf Inverse Image Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.SheafInverseImageComposition

noncomputable section

/-! Identity and composition isomorphisms for inverse image of abelian sheaves, constructed from the actual pushforward adjunctions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

variable {X Y Z : TopCat.{u}}

def additiveSheafPushforwardIdIso (X : TopCat.{u}) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 X) ≅ 𝟭 (X.Sheaf AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def additiveSheafPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} g ≅
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def additiveSheafInverseImageIdIso (X : TopCat.{u}) :
    TopCat.Sheaf.pullback AddCommGrpCat.{u} (𝟙 X) ≅ 𝟭 (X.Sheaf AddCommGrpCat.{u}) :=
  Adjunction.leftAdjointIdIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (𝟙 X))
    (additiveSheafPushforwardIdIso X)

def additiveSheafInverseImageCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback AddCommGrpCat.{u} g ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
    TopCat.Sheaf.pullback AddCommGrpCat.{u} (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (f ≫ g))
    (additiveSheafPushforwardCompIso f g)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.SheafInverseImageComposition
