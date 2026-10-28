import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.SheafInverseImageComposition

/-! # Inverse Image Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.InverseImageCoherence

noncomputable section

/-! The constant-sheaf comparison respects identity and composition of actual inverse-image functors. Coherence follows from the strict top-section pushforward comparisons by adjunction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor _root_.TopologicalSpace
universe u

variable {X Y Z : TopCat.{u}}

theorem constantSheafInverseImage_id (X : TopCat.{u}) :
    SheafInverseImage.constantSheafInverseImageIso (𝟙 X) =
      isoWhiskerLeft (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (Additive.SheafInverseImageComposition.additiveSheafInverseImageIdIso X) ≪≫
      rightUnitor (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  apply Adjunction.leftAdjointCompIso_comp_id
  ext F x
  rfl

theorem constantSheafInverseImage_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    isoWhiskerLeft (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
        (Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f g) ≪≫ SheafInverseImage.constantSheafInverseImageIso (f ≫ g) =
      (associator (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)).symm ≪≫
      isoWhiskerRight (SheafInverseImage.constantSheafInverseImageIso g)
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) ≪≫ SheafInverseImage.constantSheafInverseImageIso f := by
  apply Adjunction.leftAdjointCompIso_assoc
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u} isTerminalTop)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (f ≫ g))
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)
    (SheafInverseImage.additivePushforwardTopIso g) (Additive.SheafInverseImageComposition.additiveSheafPushforwardCompIso f g)
    (SheafInverseImage.additivePushforwardTopIso (f ≫ g)) (SheafInverseImage.additivePushforwardTopIso f)
  ext F x
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.InverseImageCoherence
