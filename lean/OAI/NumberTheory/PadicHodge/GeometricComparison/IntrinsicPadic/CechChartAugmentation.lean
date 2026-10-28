import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechChartMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestrictionChartFactorization
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.ChartAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentationFactorization

/-! # Cech Chart Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechChartAugmentation.IntrinsicPadicCechChartAugmentation

noncomputable section

/-! The canonical native chart map preserves the actual structure-sheaf
augmentation under geometric restriction of the global Cech resolution. -/

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

local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.localSheafification p X Y f n I
local notation "R" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.restriction p X Y f hp n I
local notation "T" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechTotal.IntrinsicPadicCechGeometricTotal.presheafRestriction p X Y f hp n I
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SliceDiagram.IntrinsicPadicGeometricSliceDiagram.meet_isIso p X Y f hp n I
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.val I.property n

def frameRestrictionIso := (NatIso.mapHomologicalComplex
  (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n) (.up ℕ)).app (IntegralComparison.BoundedFrame.Diagram.complex FI)

theorem presheaf_factorization :
    ((R).mapHomologicalComplex (.up ℕ)).map (((S).mapHomologicalComplex (.up ℕ)).map
      (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)) ≫
        (CechTotal.IntrinsicPadicCechGeometricTotal.iso p X Y f hp n I).hom =
    ((R).mapHomologicalComplex (.up ℕ)).map (((S).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.Diagram.augmentation FI)) ≫ (frameRestrictionIso p X Y f hp n I).hom ≫
        ((L).mapHomologicalComplex (.up ℕ)).map (Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H) :=
  Cech.TotalRestrictionChartFactorization.CechTotalRestrictionChartFactorization.factorization X.left.affineOpens I S R T L
    (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n) U
    (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n)
    (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.source p Y n) (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.cone p X Y f hp n) H

theorem sheaf_factorization :
    ((R).mapHomologicalComplex (.up ℕ)).map (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n) ≫
      (CechTotal.IntrinsicPadicCechGeometricTotal.iso p X Y f hp n I).hom =
    ((R).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.Bounded.RelativeSheafComplex.augmentation w n FI) ≫
      (frameRestrictionIso p X Y f hp n I).hom ≫
        ((L).mapHomologicalComplex (.up ℕ)).map (Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H) := by
  exact AugmentationFactorization.AugmentationFactorizationSource.functorSource ((R).mapHomologicalComplex (.up ℕ))
    (IntegralComparison.Bounded.RelativeSheafComplex.sourceIso w n).inv
    (((S).mapHomologicalComplex (.up ℕ)).map (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U))
    (((S).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedFrame.Diagram.augmentation FI))
    (CechTotal.IntrinsicPadicCechGeometricTotal.iso p X Y f hp n I).hom (frameRestrictionIso p X Y f hp n I).hom
    (((L).mapHomologicalComplex (.up ℕ)).map (Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))
    (presheaf_factorization p X Y f hp n I)

def pullbackAugmentation := (IntegralComparison.BoundedFrame.PullbackAugmentation.sourceIso g hg n).inv ≫
  ((R).mapHomologicalComplex (.up ℕ)).map (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n)

theorem augmentation :
    IntegralComparison.Bounded.RelativeSheafComplex.augmentation wI n (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n) ≫
      CechChartMap.IntrinsicPadicCechChartMap.map p X Y f hp n I = pullbackAugmentation p X Y f hp n I := by
  apply ChartAugmentation.ChartAugmentationAssembly.augmentation
    (IntegralComparison.Bounded.RelativeSheafComplex.augmentation wI n (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n))
    (IntegralComparison.BoundedFrame.PullbackAugmentation.augmentation g hg n FI)
    (pullbackAugmentation p X Y f hp n I) (frameRestrictionIso p X Y f hp n I).hom
    (CechTotal.IntrinsicPadicCechGeometricTotal.localFrameIso p X Y f hp n I)
    (((L).mapHomologicalComplex (.up ℕ)).map (Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))
    (CechTotal.IntrinsicPadicCechGeometricTotal.iso p X Y f hp n I)
  · exact IntegralComparison.BoundedFrame.SheafAugmentation.augmentation g hg n
      (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n)
  · exact AugmentationFactorization.AugmentationFactorizationSource.source
      (IntegralComparison.BoundedFrame.PullbackAugmentation.sourceIso g hg n).inv
      (((R).mapHomologicalComplex (.up ℕ)).map (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n))
      (((R).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.Bounded.RelativeSheafComplex.augmentation w n FI))
      (CechTotal.IntrinsicPadicCechGeometricTotal.iso p X Y f hp n I).hom (frameRestrictionIso p X Y f hp n I).hom
      (((L).mapHomologicalComplex (.up ℕ)).map (Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))
      (sheaf_factorization p X Y f hp n I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechChartAugmentation.IntrinsicPadicCechChartAugmentation
