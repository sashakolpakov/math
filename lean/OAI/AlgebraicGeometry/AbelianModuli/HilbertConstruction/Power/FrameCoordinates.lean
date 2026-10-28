import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.FrameRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units

/-! # Frame Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FrameCoordinates

noncomputable section

/-! Coordinates of tensor powers in line-bundle frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L : X.Modules}

/-- Taking the power of a section multiplied by a scalar endomorphism raises
that scalar endomorphism to the same power. -/
theorem tensorPowerSection_scalar (a : End (Line.Bundles.structureModule X))
    (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) :
    TensorPower.Maps.tensorPowerSection (a ≫ s) n = (a ^ n) ≫ TensorPower.Maps.tensorPowerSection s n := by
  simp only [TensorPower.Maps.tensorPowerSection, TensorPower.Maps.tensorPowerMap_comp]
  rw [← TensorPower.Units.tensorPowerMap_unit_conjugation a n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The coordinate endomorphism of a power is the corresponding power of the
original coordinate endomorphism. -/
theorem frameCoordinateEnd_tensorPowerSection (s t : Line.Bundles.structureModule X ⟶ L)
    [IsIso s] (n : ℕ) :
    Frame.Coordinates.frameCoordinateEnd (TensorPower.Maps.tensorPowerSection s n) (TensorPower.Maps.tensorPowerSection t n) =
      (Frame.Coordinates.frameCoordinateEnd s t) ^ n := by
  have he : ((Frame.Coordinates.frameCoordinateEnd s t) ^ n) ≫ TensorPower.Maps.tensorPowerSection s n = TensorPower.Maps.tensorPowerSection t n :=
    (tensorPowerSection_scalar (Frame.Coordinates.frameCoordinateEnd s t) s n).symm.trans
      (congrArg (fun a => TensorPower.Maps.tensorPowerSection a n) (Frame.Coordinates.frameCoordinateEnd_frame s t))
  apply (cancel_mono (TensorPower.Maps.tensorPowerSection s n)).mp
  exact (Frame.Coordinates.frameCoordinateEnd_frame (TensorPower.Maps.tensorPowerSection s n) (TensorPower.Maps.tensorPowerSection t n)).trans he.symm

/-- Ordinary powers of regular functions are the coordinates of tensor powers
of sections in the induced frame. -/
theorem frameCoordinate_tensorPowerSection (s t : Line.Bundles.structureModule X ⟶ L)
    [IsIso s] (n : ℕ) :
    Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection s n) (TensorPower.Maps.tensorPowerSection t n) =
      (Frame.Coordinates.frameCoordinate s t) ^ n :=
  (congrArg (Frame.Coordinates.structureModuleEndValue X) (frameCoordinateEnd_tensorPowerSection s t n)).trans
    (map_pow (Frame.Coordinates.structureModuleEndValue X) (Frame.Coordinates.frameCoordinateEnd s t) n)

/-- The power-coordinate formula is compatible with restriction to any open subscheme. -/
theorem frameCoordinate_tensorPowerSection_pullback (f : Y ⟶ X) [IsOpenImmersion f]
    (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] (n : ℕ) :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))
      (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection t n)) = (f.appTop (Frame.Coordinates.frameCoordinate s t)) ^ n := by
  exact (Frame.FrameRestriction.frameCoordinate_pullback f (TensorPower.Maps.tensorPowerSection s n) (TensorPower.Maps.tensorPowerSection t n)).trans
    ((congrArg f.appTop (frameCoordinate_tensorPowerSection s t n)).trans
      (map_pow f.appTop.hom (Frame.Coordinates.frameCoordinate s t) n))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FrameCoordinates
