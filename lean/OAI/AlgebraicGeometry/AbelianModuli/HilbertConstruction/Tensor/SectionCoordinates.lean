import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FrameCoordinates

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionCoordinates

noncomputable section

/-! Tensor-product sections multiply their frame coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M : X.Modules}

theorem tensorProductSection_scalar (a b : End (Line.Bundles.structureModule X))
    (s : Line.Bundles.structureModule X ⟶ L) (t : Line.Bundles.structureModule X ⟶ M) :
    ProductSections.tensorProductSection (a ≫ s) (b ≫ t) = (a ≫ b) ≫ ProductSections.tensorProductSection s t := by
  have h : ProductSections.tensorProductSection a b =
      (a ≫ b) ≫ (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).inv := by
    apply (cancel_mono (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom).mp
    rw [ProductSections.tensorProductSection_unit_formula, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← ProductSections.tensorProductSection_postcomp, h, Category.assoc]
  rfl

theorem frameCoordinateEnd_tensorProduct
    (e s : Line.Bundles.structureModule X ⟶ L) (f t : Line.Bundles.structureModule X ⟶ M) [IsIso e] [IsIso f] :
    Frame.Coordinates.frameCoordinateEnd (ProductSections.tensorProductSection e f) (ProductSections.tensorProductSection s t) =
      Frame.Coordinates.frameCoordinateEnd e s ≫ Frame.Coordinates.frameCoordinateEnd f t := by
  apply (cancel_mono (ProductSections.tensorProductSection e f)).mp
  rw [Frame.Coordinates.frameCoordinateEnd_frame, ← tensorProductSection_scalar,
    Frame.Coordinates.frameCoordinateEnd_frame, Frame.Coordinates.frameCoordinateEnd_frame]

theorem frameCoordinate_tensorProduct
    (e s : Line.Bundles.structureModule X ⟶ L) (f t : Line.Bundles.structureModule X ⟶ M) [IsIso e] [IsIso f] :
    Frame.Coordinates.frameCoordinate (ProductSections.tensorProductSection e f) (ProductSections.tensorProductSection s t) =
      Frame.Coordinates.frameCoordinate e s * Frame.Coordinates.frameCoordinate f t := by
  change Frame.Coordinates.structureModuleEndValue X
      (Frame.Coordinates.frameCoordinateEnd (ProductSections.tensorProductSection e f) (ProductSections.tensorProductSection s t)) = _
  rw [frameCoordinateEnd_tensorProduct]
  change Frame.Coordinates.structureModuleEndValue X (Frame.Coordinates.frameCoordinateEnd f t * Frame.Coordinates.frameCoordinateEnd e s) = _
  rw [map_mul]
  exact mul_comm _ _

theorem frameCoordinate_tensorProduct_power
    (e s : Line.Bundles.structureModule X ⟶ L) (f t : Line.Bundles.structureModule X ⟶ M)
    [IsIso e] [IsIso f] (n : ℕ) :
    Frame.Coordinates.frameCoordinate (ProductSections.tensorProductSection (TensorPower.Maps.tensorPowerSection e n) (TensorPower.Maps.tensorPowerSection f n))
      (ProductSections.tensorProductSection (TensorPower.Maps.tensorPowerSection s n) (TensorPower.Maps.tensorPowerSection t n)) =
      Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection (ProductSections.tensorProductSection e f) n)
        (TensorPower.Maps.tensorPowerSection (ProductSections.tensorProductSection s t) n) := by
  rw [frameCoordinate_tensorProduct, Power.FrameCoordinates.frameCoordinate_tensorPowerSection,
    Power.FrameCoordinates.frameCoordinate_tensorPowerSection, Power.FrameCoordinates.frameCoordinate_tensorPowerSection,
    frameCoordinate_tensorProduct, mul_pow]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionCoordinates
