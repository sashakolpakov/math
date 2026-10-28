import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.BilinearComposition

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackComposition

noncomputable section

/-!
# The canonical tensor comparison respects composition of geometric pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Transposing through geometric pullback composition uses the actual direct-image comparison. -/
theorem homEquiv_composition (M : Z.Modules) (N : X.Modules)
    (t : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
      ((Scheme.Modules.pullbackComp f g).inv.app M ≫ t) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ N t) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N := by
  exact AdjointIsoUnits.homEquiv_transport
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g)
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g) t

/-- The tensor comparison for a composite equals the two successive canonical comparisons. -/
theorem pullbackMap_comp_inv (M N : Z.Modules) :
    PullbackMap.pullbackMap (f ≫ g) M N ≫ SheafMaps.tensorMap ((Scheme.Modules.pullbackComp f g).inv.app M)
      ((Scheme.Modules.pullbackComp f g).inv.app N) =
    (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
      (Scheme.Modules.pullback f).map (PullbackMap.pullbackMap g M N) ≫
        PullbackMap.pullbackMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [PullbackMap.pullbackMap_postcomp, SheafMaps.tensorMap_bilinear, homEquiv_composition,
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, Adjunction.homEquiv_naturality_left, PullbackMap.pullbackMap_postcomp]
  erw [PullbackMap.pullbackMap_characterization f ((Scheme.Modules.pullback g).obj M)
    ((Scheme.Modules.pullback g).obj N)]
  exact (BilinearComposition.bilinearAdjoint_comp f g M N
    (SheafMaps.tensorBilinear ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)))).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackComposition
