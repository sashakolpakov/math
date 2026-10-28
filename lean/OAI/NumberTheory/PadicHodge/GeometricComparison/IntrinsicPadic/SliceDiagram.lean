import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSubcategoryMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PresheafSliceDiagram

/-! # Slice Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram

noncomputable section

/-! The actual native frame diagram contracts after restriction to each
geometric affine chart, using smooth lifts for its bounded objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.val I.property n
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose
  (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp I.val I.property)
  (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp I.val I.property) n

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem map_to_frame (T) : Nonempty ((t).obj T ⟶ FI) := by
  obtain ⟨a⟩ := FrameCover.IntrinsicPadicFrameCover.exists_map p X Y f hp n I.val I.property
    ((t).obj T).obj T.obj.mapToX rfl T.property
  exact ⟨ObjectProperty.homMk a⟩

theorem product_isIso (V : X.left.affineOpens) (T) :
    IsIso (prod.map (LocalProduct.IntrinsicPadicLocalProduct.restriction p X Y f hp n
      V.val I.val V.property I.property) (𝟙 ((t).obj T))) := by
  obtain ⟨a⟩ := map_to_frame p X Y f hp n I T
  exact LocalProduct.IntrinsicPadicLocalProduct.map_isIso p X Y f hp n V.val I.val V.property I.property ((t).obj T) a

theorem frameMap_isIso (V : X.left.affineOpens) : IsIso
    (((IntegralComparison.Relative.ComplexRestriction.restriction (B := W) t).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.Change.presheafMap
        (LocalProduct.IntrinsicPadicLocalProduct.restriction p X Y f hp n V.val I.val V.property I.property))) :=
  Frame.ChangeOnSubcategoryMap.FrameChangeOnSubcategoryMap.isIso w n t _ _
    (LocalProduct.IntrinsicPadicLocalProduct.restriction p X Y f hp n V.val I.val V.property I.property)
    (fun T => product_isIso p X Y f hp n I V T)

def diagram := (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op ⋙
  BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor w n ⋙
    (IntegralComparison.Relative.ComplexRestriction.restriction (B := W) t).mapHomologicalComplex (.up ℕ)

theorem meet_isIso (V : X.left.affineOpens) : IsIso
    ((diagram p X Y f hp n I).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) := by
  dsimp only [diagram, Functor.comp_map, Functor.op_map]
  rw [Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation.map_eq]
  erw [PresheafSliceDiagram.IntrinsicPadicPresheafSliceDiagram.restriction_eq]
  exact frameMap_isIso p X Y f hp n I V

variable {ι : Type} (U : ι → X.left.affineOpens) (i : ι)

def localHomotopyEquiv :=
  Semilattice.LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv X.left.affineOpens U i
    (diagram p X Y f hp n (U i)) (fun V => meet_isIso p X Y f hp n (U i) V)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram
