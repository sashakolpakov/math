import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TensorFrames

/-! # Frame Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FrameCoordinates

noncomputable section

/-! Change-of-frame coordinates for relative powers and tensor products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem relativePowerFrame_coordinate (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (e d : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) (n : ℕ) :
    Frame.Coordinates.frameCoordinate (PowerFrames.relativePowerFrame f L e n).hom (PowerFrames.relativePowerFrame f L d n).hom =
      Frame.Coordinates.frameCoordinate e.hom d.hom ^ n := by
  let : IsIso (Power.PullbackComparison.powerPullbackComparison f L.sheaf n) := LineBundle.PowerBaseChange.lineBundle_powerPullbackComparison_isIso f L n
  exact (Frame.FrameRestriction.frameCoordinate_targetIso (PowerFrames.relativePowerFrame f L e n).hom
    (PowerFrames.relativePowerFrame f L d n).hom (asIso (Power.PullbackComparison.powerPullbackComparison f L.sheaf n))).symm.trans
      ((Frame.FrameRestriction.frameCoordinate_congr (PowerFrames.relativePowerFrame_spec f L e n) (PowerFrames.relativePowerFrame_spec f L d n)).trans
        (Power.FrameCoordinates.frameCoordinate_tensorPowerSection e.hom d.hom n))

theorem relativeTensorFrame_coordinate (f : X ⟶ Y) (L M : Line.Bundles.LineBundle Y)
    (e e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf)
    (d d' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M.sheaf) :
    Frame.Coordinates.frameCoordinate (TensorFrames.relativeTensorFrame f L M e d).hom (TensorFrames.relativeTensorFrame f L M e' d').hom =
      Frame.Coordinates.frameCoordinate e.hom e'.hom * Frame.Coordinates.frameCoordinate d.hom d'.hom := by
  let : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f L M
  exact (Frame.FrameRestriction.frameCoordinate_targetIso (TensorFrames.relativeTensorFrame f L M e d).hom
    (TensorFrames.relativeTensorFrame f L M e' d').hom (asIso (Tensor.PullbackComparison.tensorPullbackComparison f L.sheaf M.sheaf))).symm.trans
      ((Frame.FrameRestriction.frameCoordinate_congr (TensorFrames.relativeTensorFrame_spec f L M e d)
        (TensorFrames.relativeTensorFrame_spec f L M e' d')).trans
          (Tensor.SectionCoordinates.frameCoordinate_tensorProduct e.hom e'.hom d.hom d'.hom))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FrameCoordinates
