import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechChartAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Cech Local -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechLocal.Comparison

noncomputable section

/-! On every geometric affine chart, the global native comparison
induces an original augmentation-preserving map from its local frame. -/

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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.restriction p k n X Y f hp I

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def resolution := Bounded.GeometricResolution.resolution g hg n J

def globalMap := ((R).mapHomologicalComplex (.up ℕ)).map
  (CechInjective.Comparison.map p k n X Y f hp J)

def map := CechChartMap.map p k n X Y f hp I ≫ globalMap p k n X Y f hp I J

theorem global_augmentation : CechChartAugmentation.pullbackAugmentation p k n X Y f hp I ≫
    globalMap p k n X Y f hp I J = (resolution p k n X Y f hp I J).ι :=
  (Single.ComplexTransportNaturality.comp R (BoundedOpen.Sheaves.structureTransport g hg n)
    (CechSheafResolution.augmentation p k n X Y f hp)
    (CechInjective.Comparison.map p k n X Y f hp J)).trans
      (congrArg (fun a => Single.ComplexTransport.map R (BoundedOpen.Sheaves.structureTransport g hg n) a)
        (CechInjective.Comparison.augmentation p k n X Y f hp J))

theorem augmentation :
    Bounded.RelativeSheafComplex.augmentation wI n (Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property) ≫
      Comparison.map p k n X Y f hp I J = (resolution p k n X Y f hp I J).ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ globalMap p k n X Y f hp I J)
      (CechChartAugmentation.augmentation p k n X Y f hp I)).trans
        (global_augmentation p k n X Y f hp I J))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechLocal.Comparison
