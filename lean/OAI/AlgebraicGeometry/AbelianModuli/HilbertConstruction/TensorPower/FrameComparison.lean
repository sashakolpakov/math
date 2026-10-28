import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionCoordinates

/-! # Frame Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameComparison

noncomputable section

/-! Frame-independent comparison between the power of a tensor product and the tensor product of powers on trivialized bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {A B L M : X.Modules}

theorem frameMap_eq_of_coordinate_eq
    (e e' : Line.Bundles.structureModule X ⟶ A) (f f' : Line.Bundles.structureModule X ⟶ B)
    [IsIso e] [IsIso e'] [IsIso f] [IsIso f']
    (h : Frame.Coordinates.frameCoordinate e e' = Frame.Coordinates.frameCoordinate f f') : inv e ≫ f = inv e' ≫ f' := by
  have he : Frame.Coordinates.frameCoordinateEnd e e' = Frame.Coordinates.frameCoordinateEnd f f' :=
    Global.Sections.structureModuleEndValue_injective X h
  apply (cancel_epi e').mp
  rw [IsIso.hom_inv_id_assoc]
  exact (Category.assoc e' (inv e) f).symm.trans
    ((congrArg (fun a : End (Line.Bundles.structureModule X) => a ≫ f) he).trans (Frame.Coordinates.frameCoordinateEnd_frame f f'))

def tensorPowerFrameComparisonIso
    (e : Line.Bundles.structureModule X ⟶ L) (f : Line.Bundles.structureModule X ⟶ M)
    [IsIso e] [IsIso f] (n : ℕ) :
    PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n ≅ Tensor.ProductSheaf.tensorModule (PowerSheaf.tensorPowerModule L n) (PowerSheaf.tensorPowerModule M n) :=
  (asIso (Maps.tensorPowerSection (Tensor.ProductSections.tensorProductSection e f) n)).symm ≪≫
    asIso (Tensor.ProductSections.tensorProductSection (Maps.tensorPowerSection e n) (Maps.tensorPowerSection f n))

theorem tensorPowerFrameComparisonIso_frame
    (e : Line.Bundles.structureModule X ⟶ L) (f : Line.Bundles.structureModule X ⟶ M)
    [IsIso e] [IsIso f] (n : ℕ) :
    Maps.tensorPowerSection (Tensor.ProductSections.tensorProductSection e f) n ≫ (tensorPowerFrameComparisonIso e f n).hom =
      Tensor.ProductSections.tensorProductSection (Maps.tensorPowerSection e n) (Maps.tensorPowerSection f n) := by
  change _ ≫ (inv (Maps.tensorPowerSection (Tensor.ProductSections.tensorProductSection e f) n) ≫ _) = _
  simp only [IsIso.hom_inv_id_assoc]
  rfl

theorem tensorPowerFrameComparisonIso_independent
    (e e' : Line.Bundles.structureModule X ⟶ L) (f f' : Line.Bundles.structureModule X ⟶ M)
    [IsIso e] [IsIso e'] [IsIso f] [IsIso f'] (n : ℕ) :
    tensorPowerFrameComparisonIso e f n = tensorPowerFrameComparisonIso e' f' n := by
  apply Iso.ext
  exact frameMap_eq_of_coordinate_eq _ _ _ _ (Tensor.SectionCoordinates.frameCoordinate_tensorProduct_power e e' f f' n).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameComparison
