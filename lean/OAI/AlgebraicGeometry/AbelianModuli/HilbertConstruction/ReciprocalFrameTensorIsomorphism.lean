import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReciprocalFrameTensorCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSheafificationIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

/-! # Reciprocal Frame Tensor Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Reciprocal local frame cocycles give an actual tensor-product isomorphism with the structure module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal N)

def CompatibleSheaf.CompatibleSheafFrames.reciprocalTensorBasisMap : PresheafModuleBasisMaps.PresheafModuleBasisMap (Module.OpenMapGluing.subordinateOpenBasis U)
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val) (Line.Bundles.structureModule X) where
  app V := (E.reciprocalTensorCoordinate F V.val
    (Classical.choose V.property) (Classical.choose_spec V.property)).toLinearMap
  naturality V W h x := by
    have hi := Classical.choose_spec V.property
    have hj := Classical.choose_spec W.property
    change E.reciprocalTensorCoordinate F V.val (Classical.choose V.property) hi
      ((PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val).map (homOfLE h).op x) = _
    rw [E.reciprocalTensorCoordinate_independent F V.val
      (Classical.choose V.property) (Classical.choose W.property) hi (h.trans hj)]
    exact E.reciprocalTensorCoordinate_restrict F W.val V.val h (Classical.choose W.property) hj x

def CompatibleSheaf.CompatibleSheafFrames.reciprocalTensorIso (hU : ∀ x : X, ∃ i, x ∈ U i) : Tensor.ProductSheaf.tensorModule M N ≅ Line.Bundles.structureModule X :=
  (E.reciprocalTensorBasisMap F).sheafificationIso (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)
    (fun V => (E.reciprocalTensorCoordinate F V.val
      (Classical.choose V.property) (Classical.choose_spec V.property)).bijective)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
