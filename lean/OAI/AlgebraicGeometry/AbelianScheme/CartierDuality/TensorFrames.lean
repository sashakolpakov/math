import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

/-! # Tensor Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorFrames.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: tensor products multiply actual framed scalars
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

universe u

variable {X : Scheme.{u}}

/-- The tensor unit carries tensor products of scalar endomorphisms to their composition. -/
theorem tensorUnit_scalar (a b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) :
    Picard.PoincareBundle.Tensor.SheafMaps.tensorMap a b ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom =
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom ≫ a ≫ b := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).injective
  rw [Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_precomp, Picard.PoincareBundle.Tensor.UnitPullback.tensorUnitLeft_bilinear, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, Picard.PoincareBundle.Tensor.UnitPullback.tensorUnitLeft_bilinear]
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change Γ(X, U) at x y
  change (show Γ(X, U) from a.app U x) * (show Γ(X, U) from b.app U y) = b.app U (a.app U (x * y))
  rw [AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app a U x, AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app b U y,
    AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app a U (x * y),
    AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app b U ((x * y) * (show Γ(X, U) from a.app U (1 : Γ(X, U))))]
  ring

/-- The tensor frame is the actual tensor of the two supplied line frames. -/
def tensorFrame {M N : X.Modules} (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  Picard.PoincareBundle.Tensor.UnitPullback.tensorIso e d ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

/-- Conjugating a tensor map by tensor frames tensors the two conjugated maps. -/
theorem tensorFrame_conjugation {M M' N N' : X.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (e' : M' ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d' : N' ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : M ⟶ M') (b : N ⟶ N') :
    (tensorFrame e d).inv ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap a b ≫ (tensorFrame e' d').hom =
      (e.inv ≫ a ≫ e'.hom) ≫ (d.inv ≫ b ≫ d'.hom) := by
  have ht : (tensorFrame e d).inv ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap a b ≫ (tensorFrame e' d').hom =
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).inv ≫
        Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (e.inv ≫ a ≫ e'.hom) (d.inv ≫ b ≫ d'.hom) ≫
          (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom := by
    simp only [tensorFrame, Iso.trans_inv, Iso.trans_hom, Picard.PoincareBundle.Tensor.UnitPullback.tensorIso,
      ← Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_comp, Category.assoc]
  rw [ht, tensorUnit_scalar, Iso.inv_hom_id_assoc]

/-- In regular-function coordinates, tensor products multiply the two framed scalars. -/
theorem tensorFrame_scalar {M M' N N' : X.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (e' : M' ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d' : N' ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (a : M ⟶ M') (b : N ⟶ N') :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X ((tensorFrame e d).inv ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap a b ≫ (tensorFrame e' d').hom) =
      AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (e.inv ≫ a ≫ e'.hom) * AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (d.inv ≫ b ≫ d'.hom) := by
  rw [tensorFrame_conjugation]
  let a' : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := e.inv ≫ a ≫ e'.hom
  let b' : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := d.inv ≫ b ≫ d'.hom
  exact ((AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X).map_mul b' a').trans (mul_comm _ _)

/-- The tensor frame pulls back through the canonical tensor comparison and the actual unit map. -/
theorem tensorFrame_pullback {Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (d : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (tensorFrame e d) f).hom =
      Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N ≫ (tensorFrame (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e f) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d f)).hom := by
  change (Scheme.Modules.pullback f).map (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap e.hom d.hom ≫
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)).hom) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
    Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N ≫
      Picard.PoincareBundle.Tensor.SheafMaps.tensorMap ((Scheme.Modules.pullback f).map e.hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom)
        ((Scheme.Modules.pullback f).map d.hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom) ≫
          (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom
  rw [Functor.map_comp, ← Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f M N), ← Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap_naturality]
  simp only [Category.assoc]
  rw [Picard.PoincareBundle.Tensor.UnitPullback.pullbackMap_unit_fac]

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorFrames.Construction.LineDescent
