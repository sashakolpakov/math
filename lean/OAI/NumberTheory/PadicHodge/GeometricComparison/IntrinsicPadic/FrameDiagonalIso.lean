import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.OpenSectionsIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage

/-! # Frame Diagonal Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalIso.IntrinsicPadicFrameDiagonalIso

noncomputable section

/-! The actual frame-to-diagonal section map is invertible on each affine
subchart of the integral etale cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens)

local notation "W" => WittVector p (ZMod p)
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ I.val)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C)
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "Flocal" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n
local notation "Fglobal" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.val I.property n
local notation "g" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp I.val I.property
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp I.val I.property

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance
local instance separatedLocal : IsSeparated wI := IntegralComparison.BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local instance chartOpen : IsOpenImmersion g := ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp I.val I.property

omit [IsProper X.hom] in
theorem component_eq :
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp n).app (op I) =
      BoundedFrame.OpenSectionsIso.BoundedFrameOpenSectionsIso.map n (FY := Fglobal) (f ⁻¹ᵁ I.val) := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact FrameDiagonalCoordinates.IntrinsicPadicFrameDiagonalCoordinates.app_f p X Y f hp n I k

variable (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

include hi in
theorem isIso : IsIso ((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp n).app (op I)) := by
  let e : Fglobal ≅ Fglobal := Iso.refl Fglobal
  rw [component_eq p X Y f hp n I]
  exact BoundedFrame.OpenSectionsIso.BoundedFrameOpenSectionsIso.isIso g hg n (FX := Flocal) (FY := Fglobal) e
    (SubchartResolution.IntrinsicPadicSubchartResolution.sectionsMap_isIso p X Y f hp n I i hi)
    (f ⁻¹ᵁ I.val) (ChartImage.IntrinsicPadicChartImage.opensRange p X Y f hp I.val I.property).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalIso.IntrinsicPadicFrameDiagonalIso
