import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.OpenSectionsIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SubchartResolution

/-! # Frame Diagonal Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalIso

noncomputable section

/-! The actual frame-to-diagonal section map is invertible on each affine
subchart of the integral etale cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f I.val
local instance specialAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ I.val)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "Flocal" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property
local notation "Fglobal" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp I.val I.property
local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property
local notation "hg" => (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation.overWitt p k C Y (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property) (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart_over p k n X Y f hp I.val I.property))

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance separatedLocal : IsSeparated wI := BoundedTruncated.FrameProduct.structureMap_separated p k C
local instance chartOpen : IsOpenImmersion g := Truncated.AffineModelFrame.chart_open p k n X Y f hp I.val I.property

omit [IsProper X.hom] in
theorem component_eq :
    (FrameDiagonalMap.transformation p k n X Y f hp).app (op I) =
      GeometricComparison.BoundedFrame.OpenSectionsIso.BoundedFrameOpenSectionsIso.map n (FY := Fglobal) (f ⁻¹ᵁ I.val) := by
  apply HomologicalComplex.Hom.ext
  funext degree
  exact FrameDiagonalCoordinates.app_f p k n X Y f hp I degree

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : I.val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X i).val)

include hi in
theorem isIso : IsIso ((FrameDiagonalMap.transformation p k n X Y f hp).app (op I)) := by
  let e : Fglobal ≅ Fglobal := Iso.refl Fglobal
  rw [component_eq p k n X Y f hp I]
  exact GeometricComparison.BoundedFrame.OpenSectionsIso.BoundedFrameOpenSectionsIso.isIso g hg n (FX := Flocal) (FY := Fglobal) e
    (SubchartResolution.sections_isIso p k n X Y f hp I (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.originalIndex (Truncated.Witt.Ring p k n) X i) hi)
    (f ⁻¹ᵁ I.val) (IsAffineOpen.opensRange_fromSpec (Truncated.AffineModelFrame.residue_affine p k n X Y f hp I.val I.property)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalIso
