import OAI.RepresentationTheory.Theta.Geometric.AlgebraicDifferenceBundle

/-! # Picard Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback

noncomputable section

/-! Actual pullback induces a homomorphism on the intrinsic Picard group,
using the already proved arbitrary tensor-module pullback comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def picardPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y →* AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X where
  toFun := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f
  map_one' := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial f
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b (fun L M => ?_)
    exact Quotient.sound ⟨TensorModulePullback.tensorModulePullbackIso f L.sheaf M.sheaf⟩

theorem picardPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Z) :
    picardPullback f (picardPullback g a) = picardPullback (f ≫ g) a :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp f g a).symm

theorem picardPullback_id {X : Scheme.{u}} (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    picardPullback (𝟙 X) a = a := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id a

theorem algebraicDifferenceBundle_pullback_class {X Z W : Scheme.{u}}
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (p₁ p₂ m : Z ⟶ X) (a : W ⟶ Z) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((AlgebraicDifferenceBundle.algebraicDifferenceBundle L p₁ p₂ m).pullback a) =
      picardPullback (a ≫ m) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
      (picardPullback (a ≫ p₁) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))⁻¹ *
      (picardPullback (a ≫ p₂) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))⁻¹ := by
  change picardPullback a
      (picardPullback m (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        (picardPullback p₁ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))⁻¹ *
        (picardPullback p₂ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))⁻¹) = _
  rw [map_mul, map_mul, map_inv, map_inv, picardPullback_comp, picardPullback_comp, picardPullback_comp]

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
