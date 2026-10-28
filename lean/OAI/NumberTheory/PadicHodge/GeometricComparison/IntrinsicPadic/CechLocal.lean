import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechChartAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Cech Local -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison

noncomputable section

/-! On every geometric affine chart, the global native comparison
induces an original augmentation-preserving map from its local frame. -/

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

local notation "R" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.restriction p X Y f hp n I

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def resolution := IntegralComparison.Bounded.GeometricResolution.resolution g hg n J

def globalMap := ((R).mapHomologicalComplex (.up ℕ)).map
  (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J)

def map := CechChartMap.IntrinsicPadicCechChartMap.map p X Y f hp n I ≫ globalMap p X Y f hp n I J

theorem global_augmentation : CechChartAugmentation.IntrinsicPadicCechChartAugmentation.pullbackAugmentation p X Y f hp n I ≫
    globalMap p X Y f hp n I J = (resolution p X Y f hp n I J).ι :=
  (IntegralComparison.Single.ComplexTransportNaturality.comp R (IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg n)
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n)
    (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J)).trans
      (congrArg (fun a => IntegralComparison.Single.ComplexTransport.map R (IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg n) a)
        (CechInjective.IntrinsicPadicCechInjectiveComparison.augmentation p X Y f hp n J))

theorem augmentation :
    IntegralComparison.Bounded.RelativeSheafComplex.augmentation wI n (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n) ≫
      IntrinsicPadicCechLocalComparison.map p X Y f hp n I J = (resolution p X Y f hp n I J).ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ globalMap p X Y f hp n I J)
      (CechChartAugmentation.IntrinsicPadicCechChartAugmentation.augmentation p X Y f hp n I)).trans
        (global_augmentation p X Y f hp n I J))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechLocal.IntrinsicPadicCechLocalComparison
