import OAI.RepresentationTheory.Theta.Geometric.AlgebraicPowerFrames

/-! # Power Frame Multilinear -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerFrameMultilinear

noncomputable section

/-! The canonical power frame is characterized by multiplying the actual
section coordinates. This characterization will control restriction. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def framedMultilinear {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (n : ℕ) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap M n (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers.structureModuleTensorMap X n).precomp e.hom

theorem tensorPowerGlobalFrame_spec {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (n : ℕ) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).postcomp (AlgebraicPowerFrames.tensorPowerGlobalFrame e n).hom = framedMultilinear e n := by
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).postcomp
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap e.hom n ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n).hom) = _
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec,
    ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp]
  exact congrArg (fun β => β.precomp e.hom) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitHom_spec X n)

def tensorPowerRestrictedFrame {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (e : M.restrict f ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (n : ℕ) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n).restrict f ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso f M n).symm ≪≫ AlgebraicPowerFrames.tensorPowerGlobalFrame e n

theorem tensorPowerRestrictedFrame_spec {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (e : M.restrict f ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (n : ℕ) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).restrict f).postcomp (tensorPowerRestrictedFrame f M e n).hom =
      framedMultilinear e n := by
  change ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).restrict f).postcomp
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso f M n).inv ≫ (AlgebraicPowerFrames.tensorPowerGlobalFrame e n).hom) = _
  exact (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).trans
    ((congrArg (fun β => β.postcomp (AlgebraicPowerFrames.tensorPowerGlobalFrame e n).hom)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictInv_spec f M n)).trans (tensorPowerGlobalFrame_spec e n))

end

end OAI.RepresentationTheory.Theta.Geometric.PowerFrameMultilinear
