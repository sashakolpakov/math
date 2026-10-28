import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackComposition

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackComposition

noncomputable section

/-!
# Actual bilinear line operations respect composition of geometric pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  {M N P : Z.Modules} (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)

/-- The inverse canonical tensor comparison has the exact iterated-pullback factorization. -/
theorem inverse_tensor_comp :
    Tensor.SheafMaps.tensorMap ((Scheme.Modules.pullbackComp f g).inv.app M) ((Scheme.Modules.pullbackComp f g).inv.app N) ≫
      (Tensor.LinePullback.pullbackIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
        (hM.pullback g) (hN.pullback g)).inv ≫
      (Scheme.Modules.pullback f).map (Tensor.LinePullback.pullbackIso g M N hM hN).inv =
    (Tensor.LinePullback.pullbackIso (f ≫ g) M N hM hN).inv ≫
      (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) :=
  (PullbackNaturality.inverse_square
    (Tensor.LinePullback.pullbackIso (f ≫ g) M N hM hN)
    ((Scheme.Modules.pullback f).mapIso (Tensor.LinePullback.pullbackIso g M N hM hN) ≪≫
      Tensor.LinePullback.pullbackIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
        (hM.pullback g) (hN.pullback g))
    ((Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N))
    (Tensor.SheafMaps.tensorMap ((Scheme.Modules.pullbackComp f g).inv.app M) ((Scheme.Modules.pullbackComp f g).inv.app N))
    (Tensor.PullbackComposition.pullbackMap_comp_inv f g M N).symm).symm

/-- The actual bilinear map pulled twice agrees with the composite pullback through all three canonical fiber comparisons. -/
theorem pullback_comp (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    Transport.transport
      (BilinearPullback.pullback f (hM.pullback g) (hN.pullback g) (BilinearPullback.pullback g hM hN β))
      ((Scheme.Modules.pullbackComp f g).app M) ((Scheme.Modules.pullbackComp f g).app N)
      ((Scheme.Modules.pullbackComp f g).app P) = BilinearPullback.pullback (f ≫ g) hM hN β := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change BilinearPullback.toHom _ = BilinearPullback.toHom _
  rw [Transport.toHom_transport, BilinearPullback.toHom_pullback, BilinearPullback.toHom_pullback]
  unfold BilinearPullback.pulledHom
  rw [BilinearPullback.toHom_pullback]
  unfold BilinearPullback.pulledHom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 1 3 => exact inverse_tensor_comp f g hM hN
  slice_lhs 2 3 => exact ((Scheme.Modules.pullbackComp f g).inv.naturality (BilinearPullback.toHom β)).symm
  simp only [Category.assoc]
  change (Tensor.LinePullback.pullbackIso (f ≫ g) M N hM hN).inv ≫
    (Scheme.Modules.pullback (f ≫ g)).map (BilinearPullback.toHom β) ≫
      ((Scheme.Modules.pullbackComp f g).app P).inv ≫ ((Scheme.Modules.pullbackComp f g).app P).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackComposition
