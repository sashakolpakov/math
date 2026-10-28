import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackGluing

/-! # Recovery Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.RecoveryGluing

noncomputable section

/-!
# Tensoring two actual line recoveries preserves their full geometric gluing equations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (M N : Y.Modules) (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
  {A B : X.Modules} (a : (Scheme.Modules.pullback f).obj M ⟶ A) (b : (Scheme.Modules.pullback f).obj N ⟶ B)
  (σA : (Scheme.Modules.pullback p).obj A ⟶ (Scheme.Modules.pullback q).obj A)
  (σB : (Scheme.Modules.pullback p).obj B ⟶ (Scheme.Modules.pullback q).obj B)
  (ha : (Scheme.Modules.pullback p).map a ≫ σA =
    (Cech.MateNormalization.standardGluing f p q h).hom.app M ≫ (Scheme.Modules.pullback q).map a)
  (hb : (Scheme.Modules.pullback p).map b ≫ σB =
    (Cech.MateNormalization.standardGluing f p q h).hom.app N ≫ (Scheme.Modules.pullback q).map b)

include hM hN ha hb in
/-- The canonical tensor of recovered input maps satisfies the exact ordinary geometric gluing square. -/
theorem tensor_compatible :
    (Scheme.Modules.pullback p).map (PullbackMap.pullbackMap f M N ≫ SheafMaps.tensorMap a b) ≫
      PullbackMap.pullbackMap p A B ≫ SheafMaps.tensorMap σA σB =
    (Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
      (Scheme.Modules.pullback q).map (PullbackMap.pullbackMap f M N ≫ SheafMaps.tensorMap a b) ≫ PullbackMap.pullbackMap q A B := by
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [PullbackMap.pullbackMap_naturality p a b]
  slice_rhs 3 4 => rw [PullbackMap.pullbackMap_naturality q a b]
  slice_lhs 3 4 => rw [SheafMaps.tensorMap_comp, ha, hb, ← SheafMaps.tensorMap_comp]
  have hc := congrArg (fun t => t ≫ SheafMaps.tensorMap ((Scheme.Modules.pullback q).map a) ((Scheme.Modules.pullback q).map b))
    (congrArg Iso.hom (PullbackGluing.gluing_iso f p q h M N hM hN))
  change (((Scheme.Modules.pullback p).map (PullbackMap.pullbackMap f M N) ≫
      PullbackMap.pullbackMap p ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)) ≫
      SheafMaps.tensorMap ((Cech.MateNormalization.standardGluing f p q h).hom.app M) ((Cech.MateNormalization.standardGluing f p q h).hom.app N)) ≫
      SheafMaps.tensorMap ((Scheme.Modules.pullback q).map a) ((Scheme.Modules.pullback q).map b) =
    ((Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
      ((Scheme.Modules.pullback q).map (PullbackMap.pullbackMap f M N) ≫
        PullbackMap.pullbackMap q ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))) ≫
      SheafMaps.tensorMap ((Scheme.Modules.pullback q).map a) ((Scheme.Modules.pullback q).map b) at hc
  simpa only [Category.assoc] using hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.RecoveryGluing
