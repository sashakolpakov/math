import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorSymmetrySections

/-! # Pullback Swap -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackSwap

noncomputable section

/-! The canonical tensor pullback comparison preserves interchange of the two factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

theorem map_swap {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).hom ≫ PullbackMap.pullbackMap f N M =
      PullbackMap.pullbackMap f M N ≫
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [Adjunction.homEquiv_naturality_left, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction.tensorModuleCommIso_bilinear, ← AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear_postcomp, ← Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp,
    PullbackMap.pullbackMap_characterization, PullbackMap.pullbackMap_postcomp, AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction.tensorModuleCommIso_bilinear,
    AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear_bilinearAdjoint]
  rfl

theorem iso_swap {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) :
    (Scheme.Modules.pullback f).mapIso (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N) ≪≫ LinePullback.pullbackIso f N M hN hM =
      LinePullback.pullbackIso f M N hM hN ≪≫
        AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  apply Iso.ext
  exact map_swap f M N

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackSwap
