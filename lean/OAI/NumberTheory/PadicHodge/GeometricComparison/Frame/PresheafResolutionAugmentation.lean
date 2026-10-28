import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor

/-! # Presheaf Resolution Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation

noncomputable section

/-! The original presheaf frame augmentation is natural before sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)

theorem map_eq {F G : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : G ⟶ F) :
    (BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor f n).map α.op = IntegralComparison.BoundedFrame.Change.presheafMap α := rfl

def augmentation : (Functor.const _).obj
    ((CochainComplex.single₀ _).obj
      ((IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n).op ⋙ IntegralComparison.BigCrystallineCohomology.modulePresheaf f)) ⟶
      BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor f n where
  app F := IntegralComparison.BoundedFrame.Diagram.augmentation F.unop
  naturality _ _ α := (Category.id_comp _).trans (IntegralComparison.BoundedFrame.Change.presheaf_augmentation α.unop).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation
