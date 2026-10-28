import OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullbackIso
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup
import Mathlib.Algebra.Category.Grp.Basic

/-! # Scheme Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback

noncomputable section

/-! Pullback on the intrinsic scheme Picard group, over arbitrary schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

local instance schemePicardPullbackLocal1 : MonoidalCategory Y.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

/-- Pullback commutes with tensor product without an open-immersion or flatness hypothesis. -/
def tensorModuleArbitraryPullbackIso (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app (M.val ⊗ N.val) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (PresheafTensorPullbackIso.Construction.presheafTensorPullbackIso f M.val N.val) ≪≫
    TensorSheafification.Construction.tensorSheafifyIso ((PresheafTensorPullback.Construction.modulePresheafPullback f).obj M.val) ((PresheafTensorPullback.Construction.modulePresheafPullback f).obj N.val) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((SheafOfModules.pullbackIso f.toRingCatSheafHom).app M).symm
      ((SheafOfModules.pullbackIso f.toRingCatSheafHom).app N).symm

theorem pullbackClass_mul (a b : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (a * b) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f a * AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f b := by
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M => exact Quotient.sound ⟨tensorModuleArbitraryPullbackIso f L.sheaf M.sheaf⟩

/-- The group homomorphism induced by actual line-bundle pullback. -/
def schemePicardPullback : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X where
  toFun := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f
  map_one' := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial f
  map_mul' := pullbackClass_mul f

/-- The Picard group as a contravariant functor on all schemes. -/
def schemePicardFunctor : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj X := CommGrpCat.of (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.unop)
  map f := CommGrpCat.ofHom (schemePicardPullback f.unop)
  map_id X := by
    ext q
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q
  map_comp f g := by
    ext q
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp g.unop f.unop q

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
