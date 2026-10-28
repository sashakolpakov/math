import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafRestriction

/-! # Cech Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal

noncomputable section

/-! The original global native Čech resolution restricts to the
sheafified geometric chart diagram, with the actual comparison maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ I.val)
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C)
local notation "g" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp I.val I.property
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp I.val I.property
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram.diagram p X Y f hp n I

local instance localSeparated : IsSeparated wI := IntegralComparison.BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local instance globalSeparated : IsSeparated w := by dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp I.val I.property

abbrev restriction := IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := Ideal.span {(p : W)}) (δ := γ) g hg n
abbrev presheafRestriction := IntegralComparison.Relative.ComplexRestriction.restriction (B := W)
  (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := Ideal.span {(p : W)}) (δ := γ) g hg n)
abbrev localSheafification := IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) wI n

def total := ((localSheafification p X Y f n I).mapHomologicalComplex (.up ℕ)).obj
  (CechCone.Total.CechConeTotal.total U P)

def iso : ((restriction p X Y f hp n I).mapHomologicalComplex (.up ℕ)).obj
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n) ≅ total p X Y f hp n I :=
  Cech.TotalRestriction.CechTotalRestrictionComparison.iso
    (IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)
    (restriction p X Y f hp n I) (presheafRestriction p X Y f hp n I)
    (localSheafification p X Y f n I)
    (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n) U
    (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n)

def localFrameIso : ((localSheafification p X Y f n I).mapHomologicalComplex (.up ℕ)).obj ((P).obj (op I)) ≅
    IntegralComparison.Bounded.RelativeSheafComplex.complex wI n (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n) :=
  ((localSheafification p X Y f n I).mapHomologicalComplex (.up ℕ)).mapIso
    (IntegralComparison.BoundedFrame.OpenRestriction.presheafIso g hg n (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal
