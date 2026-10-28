import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafRestriction

/-! # Cech Geometric Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal

noncomputable section

/-! The original global native Čech resolution restricts to the
sheafified geometric chart diagram, with the actual comparison maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f I.val
local instance specialAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ I.val)
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property
local notation "hg" => (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation.overWitt p k C Y (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X Y f hp I.val I.property) (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart_over p k n X Y f hp I.val I.property))
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram.diagram p k n X Y f hp I

local instance localSeparated : IsSeparated wI := BoundedTruncated.FrameProduct.structureMap_separated p k C
local instance globalSeparated : IsSeparated w := by dsimp only [Witt.Crystalline.wittStructureMap]; infer_instance
local instance chartOpen : IsOpenImmersion g := Truncated.AffineModelFrame.chart_open p k n X Y f hp I.val I.property

abbrev restriction := Bounded.PostcomposeTopology.restriction (p := p) (J := Ideal.span {(p : W)}) (δ := γ) g hg n
abbrev presheafRestriction := Relative.ComplexRestriction.restriction (B := W)
  (BoundedOpen.Equivalence.postcompose (p := p) (J := Ideal.span {(p : W)}) (δ := γ) g hg n)
abbrev localSheafification := Bounded.RelativeSheafComplex.sheafification (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) wI n

def total := ((localSheafification p k n X Y f I).mapHomologicalComplex (.up ℕ)).obj
  (GeometricComparison.CechCone.Total.CechConeTotal.total U P)

def iso : ((restriction p k n X Y f hp I).mapHomologicalComplex (.up ℕ)).obj
    (CechSheafResolution.complex p k n X Y f hp) ≅ total p k n X Y f hp I :=
  GeometricComparison.Cech.TotalRestriction.CechTotalRestrictionComparison.iso
    (Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)
    (restriction p k n X Y f hp I) (presheafRestriction p k n X Y f hp I)
    (localSheafification p k n X Y f I)
    (BoundedFrame.SheafRestriction.sheafificationIso g hg n) U
    (CechPresheaf.diagram p k n X Y f hp)

def localFrameIso : ((localSheafification p k n X Y f I).mapHomologicalComplex (.up ℕ)).obj ((P).obj (op I)) ≅
    Bounded.RelativeSheafComplex.complex wI n (Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property) :=
  ((localSheafification p k n X Y f I).mapHomologicalComplex (.up ℕ)).mapIso
    (BoundedFrame.OpenRestriction.presheafIso g hg n (Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal
