import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PresheafResolutionAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total

/-! # Cech Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf

noncomputable section

/-! The actual affine frames of a smooth truncated model assemble into
an augmented Čech complex on its original crystalline site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y

abbrev Presheaves := (BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n)ᵒᵖ ⥤ ModuleCat.{0} W

local notation "PS" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.Presheaves p k n Y

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def source : CochainComplex PS ℕ := (CochainComplex.single₀ PS).obj
  ((BoundedCrystalline.Site.inclusion w n).op ⋙ BigCrystallineCohomology.modulePresheaf w)

def diagram : X.left.affineOpensᵒᵖ ⥤ CochainComplex PS ℕ :=
  (FrameFunctor.functor p k n X Y f hp).op ⋙
    GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor w n

def cone : (Functor.const X.left.affineOpensᵒᵖ).obj (source p k n Y) ⟶ diagram p k n X Y f hp :=
  Functor.whiskerLeft (FrameFunctor.functor p k n X Y f hp).op
    (GeometricComparison.Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation.augmentation w n)

variable {ι : Type} (U : ι → X.left.affineOpens)

def total : CochainComplex PS ℕ := GeometricComparison.CechCone.Total.CechConeTotal.total U (diagram p k n X Y f hp)

def augmentation : source p k n Y ⟶ total p k n X Y f hp U :=
  GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (diagram p k n X Y f hp) (source p k n Y) (cone p k n X Y f hp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf
