import OAI.RepresentationTheory.Theta.Geometric.PowerFrameMultilinear

/-! # Global Power Frame Restriction -/

namespace OAI.RepresentationTheory.Theta.Geometric.GlobalPowerFrameRestriction

noncomputable section

/-! Restriction preserves the multiplication of frame coordinates and the
induced native tensor-power frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

theorem structureTensorMap_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (n : ℕ) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers.structureModuleTensorMap Y n).restrict f).postcomp (Scheme.Modules.restrictUnitIso f).hom =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers.structureModuleTensorMap X n).precomp (Scheme.Modules.restrictUnitIso f).hom := by
  ext U s
  change (Fin n → Γ(Y, f ''ᵁ U)) at s
  change (f.appIso U).hom (∏ i, s i) = ∏ i, (f.appIso U).hom (s i)
  exact map_prod (f.appIso U).hom.hom _ _

theorem framedMultilinear_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (n : ℕ) :
    ((PowerFrameMultilinear.framedMultilinear e n).restrict f).postcomp (Scheme.Modules.restrictUnitIso f).hom =
      PowerFrameMultilinear.framedMultilinear ((Scheme.Modules.restrictFunctor f).mapIso e ≪≫ Scheme.Modules.restrictUnitIso f) n := by
  unfold PowerFrameMultilinear.framedMultilinear
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.restrict_precomp, ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp,
    structureTensorMap_restrict, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp]
  rfl

theorem tensorPowerGlobalFrame_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (n : ℕ) :
    (PowerFrameMultilinear.tensorPowerRestrictedFrame f M
      ((Scheme.Modules.restrictFunctor f).mapIso e ≪≫ Scheme.Modules.restrictUnitIso f) n).hom =
    (Scheme.Modules.restrictFunctor f).map (AlgebraicPowerFrames.tensorPowerGlobalFrame e n).hom ≫
      (Scheme.Modules.restrictUnitIso f).hom := by
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrict_hom_ext f M n
  rw [PowerFrameMultilinear.tensorPowerRestrictedFrame_spec, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp,
    ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.restrict_postcomp, PowerFrameMultilinear.tensorPowerGlobalFrame_spec]
  exact (framedMultilinear_restrict f e n).symm

end

end OAI.RepresentationTheory.Theta.Geometric.GlobalPowerFrameRestriction
