import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleFrameMapTransport

/-! # Sum Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumFrames

noncomputable section

/-! Frame-independent local comparisons between a power of degree m+n and the tensor product of the two powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

def powerSumFrame (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) (m n : ℕ) :
    Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj
      (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L.sheaf m) (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)) :=
  Relative.TensorFrames.relativeTensorFrame f (L.tensorPower m) (L.tensorPower n)
    (Relative.PowerFrames.relativePowerFrame f L e m) (Relative.PowerFrames.relativePowerFrame f L e n)

theorem powerSumFrame_coordinate (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (e d : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) (m n : ℕ) :
    Frame.Coordinates.frameCoordinate (powerSumFrame f L e m n).hom (powerSumFrame f L d m n).hom =
      Frame.Coordinates.frameCoordinate e.hom d.hom ^ (m + n) :=
  (Relative.FrameCoordinates.relativeTensorFrame_coordinate f (L.tensorPower m) (L.tensorPower n)
    (Relative.PowerFrames.relativePowerFrame f L e m) (Relative.PowerFrames.relativePowerFrame f L d m)
    (Relative.PowerFrames.relativePowerFrame f L e n) (Relative.PowerFrames.relativePowerFrame f L d n)).trans
      ((congrArg₂ (fun a b : Γ(X, ⊤) => a * b) (Relative.FrameCoordinates.relativePowerFrame_coordinate f L e d m)
        (Relative.FrameCoordinates.relativePowerFrame_coordinate f L e d n)).trans (pow_add _ m n).symm)

def localPowerSumIso (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) (m n : ℕ) :
    (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L.sheaf (m + n)) ≅
      (Scheme.Modules.pullback f).obj
        (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L.sheaf m) (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)) :=
  (Relative.PowerFrames.relativePowerFrame f L e (m + n)).symm ≪≫ powerSumFrame f L e m n

theorem localPowerSumIso_independent (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (e d : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) (m n : ℕ) :
    localPowerSumIso f L e m n = localPowerSumIso f L d m n := by
  apply Iso.ext
  change (Relative.PowerFrames.relativePowerFrame f L e (m + n)).inv ≫ (powerSumFrame f L e m n).hom =
    (Relative.PowerFrames.relativePowerFrame f L d (m + n)).inv ≫ (powerSumFrame f L d m n).hom
  have he := IsIso.inv_eq_of_hom_inv_id (Relative.PowerFrames.relativePowerFrame f L e (m + n)).hom_inv_id
  have hd := IsIso.inv_eq_of_hom_inv_id (Relative.PowerFrames.relativePowerFrame f L d (m + n)).hom_inv_id
  simpa only [he, hd] using TensorPower.FrameComparison.frameMap_eq_of_coordinate_eq _ _ _ _
    ((Relative.FrameCoordinates.relativePowerFrame_coordinate f L e d (m + n)).trans (powerSumFrame_coordinate f L e d m n).symm)

theorem powerSumFrame_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line.Bundles.LineBundle Z)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj L.sheaf) (m n : ℕ) :
    Ample.LineBundles.pullbackSection f (powerSumFrame g L e m n).hom ≫
      (Scheme.Modules.pullbackComp f g).hom.app
        (Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L.sheaf m) (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)) =
      (powerSumFrame (f ≫ g) L (Relative.PowerFrames.compositeBundleFrame f g L e) m n).hom := by
  have hm : Relative.PowerFrames.compositeBundleFrame f g (L.tensorPower m) (Relative.PowerFrames.relativePowerFrame g L e m) =
      Relative.PowerFrames.relativePowerFrame (f ≫ g) L (Relative.PowerFrames.compositeBundleFrame f g L e) m :=
    Iso.ext (Relative.PowerFrames.relativePowerFrame_comp f g L e m)
  have hn : Relative.PowerFrames.compositeBundleFrame f g (L.tensorPower n) (Relative.PowerFrames.relativePowerFrame g L e n) =
      Relative.PowerFrames.relativePowerFrame (f ≫ g) L (Relative.PowerFrames.compositeBundleFrame f g L e) n :=
    Iso.ext (Relative.PowerFrames.relativePowerFrame_comp f g L e n)
  exact (Relative.TensorFrames.relativeTensorFrame_comp f g (L.tensorPower m) (L.tensorPower n)
    (Relative.PowerFrames.relativePowerFrame g L e m) (Relative.PowerFrames.relativePowerFrame g L e n)).trans
      (congrArg₂ (fun a b => (Relative.TensorFrames.relativeTensorFrame (f ≫ g) (L.tensorPower m) (L.tensorPower n) a b).hom) hm hn)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumFrames
