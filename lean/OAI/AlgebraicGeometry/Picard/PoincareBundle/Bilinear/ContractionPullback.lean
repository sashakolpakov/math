import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LeftUnitPullback

/-! # Contraction Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

noncomputable section

/-!
# Inserting normalized sections into bilinear maps commutes with arbitrary pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackNaturality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) (hN : Line.Bundles.IsLine N)

/-- Pullback of the tensor unit is the canonical tensor pullback followed by the actual unit maps. -/
theorem unitIso_factorization :
    (Scheme.Modules.pullback f).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso N) =
      Tensor.LinePullback.pullbackIso f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) N (Line.Bundles.isLine_unit Y) hN ≪≫
        Tensor.UnitPullback.tensorIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) (Iso.refl ((Scheme.Modules.pullback f).obj N)) ≪≫
          AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso ((Scheme.Modules.pullback f).obj N) := by
  apply Iso.ext
  exact (Tensor.LeftUnitPullback.pullbackMap_leftUnit_fac f N).symm

/-- The inverse unit comparison is expressed by the inverse canonical tensor pullback map. -/
theorem unitIso_inverse :
    (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso N).inv =
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso ((Scheme.Modules.pullback f).obj N)).inv ≫
        Tensor.SheafMaps.tensorMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv (𝟙 ((Scheme.Modules.pullback f).obj N)) ≫
          (Tensor.LinePullback.pullbackIso f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) N (Line.Bundles.isLine_unit Y) hN).inv :=
  congrArg Iso.inv (unitIso_factorization f N hN)

variable {N} {M P : Y.Modules} (hM : Line.Bundles.IsLine M)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M)

/-- The inserted section pulls back through the actual structure-sheaf unit isomorphism. -/
def pulledSection : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s

/-- Pulling back a contraction gives contraction of the pulled-back bilinear map by the pulled-back section. -/
theorem contractLeft_pullback :
    (Scheme.Modules.pullback f).map (Contraction.contractLeft β s) =
      Contraction.contractLeft (BilinearPullback.pullback f hM hN β) (pulledSection f s) := by
  unfold Contraction.contractLeft
  rw [Functor.map_comp, Functor.map_comp, unitIso_inverse f N hN, BilinearPullback.toHom_pullback]
  unfold BilinearPullback.pulledHom
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    exact PullbackNaturality.inverse_comparison_naturality f (M' := AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (N' := N)
      hM hN (Line.Bundles.isLine_unit Y) hN s (𝟙 N)
  rw [(Scheme.Modules.pullback f).map_id]
  slice_lhs 2 3 => rw [Tensor.SheafMaps.tensorMap_comp, Category.id_comp]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback
