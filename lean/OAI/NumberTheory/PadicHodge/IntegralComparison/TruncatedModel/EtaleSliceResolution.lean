import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.FrameSliceQuasiIso

/-! # Etale Slice Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.EtaleSliceResolution

noncomputable section

/-! Every affine subchart of a native finite-level étale coordinate
chart resolves functions on the slice of its original global frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : X.left.affineOpens)
  (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : I.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X i)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X I.val
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f I.val
local notation "σ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex S X i

local instance sourceAlgebra : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X I.val
local instance targetAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ I.val)
local instance sourceSmooth : Algebra.Smooth S A :=
  Truncated.AffineModelFrame.source_smooth p k n X I.val I.property

local notation "fI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "FI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp I.val I.property

local instance separated : IsSeparated fI :=
  BoundedTruncated.FrameProduct.structureMap_separated p k C

local instance globalSeparated : IsSeparated (Witt.Crystalline.wittStructureMap p k Y) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

include hi in
theorem onSlice : QuasiIso
    (((GeometricComparison.PresheafRestriction.PresheafRestrictionQuasiIso.restriction (V := ModuleCat.{0} (WittVector p k))
      (Over.forget G)).mapHomologicalComplex (.up ℕ)).map
        (BoundedFrame.Diagram.augmentation G)) := by
  let : IsSeparated fI := BoundedTruncated.FrameProduct.structureMap_separated p k C
  let : Algebra (MvPolynomial σ S) A := AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.polynomialAlgebra S X I i hi
  let : IsScalarTower S (MvPolynomial σ S) A := AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.tower S X I i hi
  let : Algebra.Etale (MvPolynomial σ S) A := AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.etale S X I i hi
  let : QuasiIso (BoundedFrame.Diagram.augmentation FI) :=
    BoundedTruncated.Resolution.presheaf_augmentation_quasiIso p k n A C σ
      (Truncated.AffineModelFrame.reduction p k n X Y f I.val)
      (Truncated.AffineModelFrame.reduction_surjective p k n X Y f hp I.val I.property)
      (Truncated.AffineModelFrame.reduction_kernel p k n X Y f hp I.val I.property)
      (Truncated.AffineModelFrame.reduction_base p k n X Y f hp I.val I.property)
  exact GeometricComparison.FrameSliceQuasiIso.OpenFrameSliceQuasiIso.onSlice
    (Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property)
    (Crystalline.OpenPresentation.overWitt p k C Y
      (Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property)
      (Truncated.AffineModelFrame.chart_over p k n X Y f hp I.val I.property)) n FI

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.EtaleSliceResolution
