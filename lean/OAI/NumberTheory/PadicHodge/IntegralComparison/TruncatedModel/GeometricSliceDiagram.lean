import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSubcategoryMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafSliceDiagram

/-! # Geometric Slice Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram

noncomputable section

/-! The actual native frame diagram contracts after restriction to each
geometric affine chart, using smooth lifts for its bounded objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "FI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp I.val I.property
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f I.val
local instance specialAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ I.val)
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose
  (Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property)
  ((Crystalline.OpenPresentation.overWitt p k C Y (Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property) (Truncated.AffineModelFrame.chart_over p k n X Y f hp I.val I.property))) n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem map_to_frame (T) : Nonempty ((t).obj T ⟶ FI) := by
  obtain ⟨a⟩ := FrameCover.exists_map p k n X Y f hp I.val I.property
    ((t).obj T).obj T.obj.mapToX rfl T.property
  exact ⟨ObjectProperty.homMk a⟩

theorem product_isIso (V : X.left.affineOpens) (T) :
    IsIso (prod.map (LocalProduct.restriction p k n X Y f hp
      V.val I.val V.property I.property) (𝟙 ((t).obj T))) := by
  obtain ⟨a⟩ := map_to_frame p k n X Y f hp I T
  exact LocalProduct.map_isIso p k n X Y f hp V.val I.val V.property I.property ((t).obj T) a

theorem frameMap_isIso (V : X.left.affineOpens) : IsIso
    (((Relative.ComplexRestriction.restriction (B := W) t).mapHomologicalComplex (.up ℕ)).map
      (BoundedFrame.Change.presheafMap
        (LocalProduct.restriction p k n X Y f hp V.val I.val V.property I.property))) :=
  GeometricComparison.Frame.ChangeOnSubcategoryMap.FrameChangeOnSubcategoryMap.isIso w n t _ _
    (LocalProduct.restriction p k n X Y f hp V.val I.val V.property I.property)
    (fun T => product_isIso p k n X Y f hp I V T)

def diagram := (FrameFunctor.functor p k n X Y f hp).op ⋙
  GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor w n ⋙
    (Relative.ComplexRestriction.restriction (B := W) t).mapHomologicalComplex (.up ℕ)

theorem meet_isIso (V : X.left.affineOpens) : IsIso
    ((diagram p k n X Y f hp I).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) := by
  dsimp only [diagram, Functor.comp_map, Functor.op_map]
  rw [GeometricComparison.Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation.map_eq]
  erw [PresheafSliceDiagram.restriction_eq]
  exact frameMap_isIso p k n X Y f hp I V

variable {ι : Type} (U : ι → X.left.affineOpens) (i : ι)

def localHomotopyEquiv :=
  GeometricComparison.Semilattice.LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv X.left.affineOpens U i
    (diagram p k n X Y f hp (U i)) (fun V => meet_isIso p k n X Y f hp (U i) V)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram
