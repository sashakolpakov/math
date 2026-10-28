import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

/-! # Left Unit Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LeftUnitPullback

noncomputable section

/-!
# The canonical tensor pullback comparison preserves the scalar unit action
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

/-- The adjoint of a pulled-back morphism is the original morphism followed by the unit. -/
theorem homEquiv_map {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {M N : C} (t : M ⟶ N) : a.homEquiv M (L.obj N) (L.map t) = t ≫ a.unit.app N := by
  have h := a.homEquiv_naturality_left t (𝟙 (L.obj N))
  rw [Category.comp_id, a.homEquiv_id] at h
  exact h

end

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules)

/-- The pullback unit respects the scalar bilinear action through the actual structure-sheaf map. -/
theorem scalar_unit :
    ((UnitPullback.scalarBilinear ((Scheme.Modules.pullback f).obj N)).pushforward f).precomp
      (UnitPullback.baseUnitMap f) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) =
    (UnitPullback.scalarBilinear N).postcomp ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) := by
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro n
  have h := (AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) U).map_smul (r : Γ(Y, U)) n
  exact h.symm

/-- The canonical tensor pullback comparison preserves the left unit isomorphism on every module sheaf. -/
theorem pullbackMap_leftUnit_fac :
    PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) N ≫
      SheafMaps.tensorMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj N)) ≫
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso ((Scheme.Modules.pullback f).obj N)).hom =
    (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso N).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) N _).injective
  rw [PullbackMap.pullbackMap_postcomp, SheafMaps.tensorMap_precomp, UnitPullback.tensorUnitLeft_bilinear,
    homEquiv_map, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, UnitPullback.tensorUnitLeft_bilinear]
  unfold PullbackMap.bilinearAdjoint
  rw [PullbackMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, UnitPullback.unitIso_unit,
    (Scheme.Modules.pushforward f).map_id, Category.comp_id]
  exact scalar_unit f N

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LeftUnitPullback
