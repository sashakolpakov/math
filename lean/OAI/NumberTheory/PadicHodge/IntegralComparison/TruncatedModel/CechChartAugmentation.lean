import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechChartMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestrictionChartFactorization
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.ChartAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentationFactorization

/-! # Cech Chart Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechChartAugmentation

noncomputable section

/-! The canonical native chart map preserves the actual structure-sheaf
augmentation under geometric restriction of the global Cech resolution. -/

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

local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.localSheafification p k n X Y f I
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.restriction p k n X Y f hp I
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechGeometricTotal.presheafRestriction p k n X Y f hp I
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GeometricSliceDiagram.meet_isIso p k n X Y f hp I
local notation "FI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp I.val I.property

def frameRestrictionIso := (NatIso.mapHomologicalComplex
  (BoundedFrame.SheafRestriction.sheafificationIso g hg n) (.up ℕ)).app (BoundedFrame.Diagram.complex FI)

theorem presheaf_factorization :
    ((R).mapHomologicalComplex (.up ℕ)).map (((S).mapHomologicalComplex (.up ℕ)).map
      (CechPresheaf.augmentation p k n X Y f hp U)) ≫
        (CechGeometricTotal.iso p k n X Y f hp I).hom =
    ((R).mapHomologicalComplex (.up ℕ)).map (((S).mapHomologicalComplex (.up ℕ)).map
      (BoundedFrame.Diagram.augmentation FI)) ≫ (frameRestrictionIso p k n X Y f hp I).hom ≫
        ((L).mapHomologicalComplex (.up ℕ)).map (GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H) :=
  GeometricComparison.Cech.TotalRestrictionChartFactorization.CechTotalRestrictionChartFactorization.factorization X.left.affineOpens I S R T L
    (BoundedFrame.SheafRestriction.sheafificationIso g hg n) U
    (CechPresheaf.diagram p k n X Y f hp)
    (CechPresheaf.source p k n Y) (CechPresheaf.cone p k n X Y f hp) H

theorem sheaf_factorization :
    ((R).mapHomologicalComplex (.up ℕ)).map (CechSheafResolution.augmentation p k n X Y f hp) ≫
      (CechGeometricTotal.iso p k n X Y f hp I).hom =
    ((R).mapHomologicalComplex (.up ℕ)).map (Bounded.RelativeSheafComplex.augmentation w n FI) ≫
      (frameRestrictionIso p k n X Y f hp I).hom ≫
        ((L).mapHomologicalComplex (.up ℕ)).map (GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H) := by
  exact GeometricComparison.AugmentationFactorization.AugmentationFactorizationSource.functorSource ((R).mapHomologicalComplex (.up ℕ))
    (Bounded.RelativeSheafComplex.sourceIso w n).inv
    (((S).mapHomologicalComplex (.up ℕ)).map (CechPresheaf.augmentation p k n X Y f hp U))
    (((S).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.Diagram.augmentation FI))
    (CechGeometricTotal.iso p k n X Y f hp I).hom (frameRestrictionIso p k n X Y f hp I).hom
    (((L).mapHomologicalComplex (.up ℕ)).map (GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))
    (presheaf_factorization p k n X Y f hp I)

def pullbackAugmentation := (BoundedFrame.PullbackAugmentation.sourceIso g hg n).inv ≫
  ((R).mapHomologicalComplex (.up ℕ)).map (CechSheafResolution.augmentation p k n X Y f hp)

theorem augmentation :
    Bounded.RelativeSheafComplex.augmentation wI n (Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property) ≫
      CechChartMap.map p k n X Y f hp I = pullbackAugmentation p k n X Y f hp I := by
  apply GeometricComparison.ChartAugmentation.ChartAugmentationAssembly.augmentation
    (Bounded.RelativeSheafComplex.augmentation wI n (Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property))
    (BoundedFrame.PullbackAugmentation.augmentation g hg n FI)
    (pullbackAugmentation p k n X Y f hp I) (frameRestrictionIso p k n X Y f hp I).hom
    (CechGeometricTotal.localFrameIso p k n X Y f hp I)
    (((L).mapHomologicalComplex (.up ℕ)).map (GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))
    (CechGeometricTotal.iso p k n X Y f hp I)
  · exact BoundedFrame.SheafAugmentation.augmentation g hg n
      (Truncated.AffineModelFrame.localFrame p k n X Y f hp I.val I.property)
  · exact GeometricComparison.AugmentationFactorization.AugmentationFactorizationSource.source
      (BoundedFrame.PullbackAugmentation.sourceIso g hg n).inv
      (((R).mapHomologicalComplex (.up ℕ)).map (CechSheafResolution.augmentation p k n X Y f hp))
      (((R).mapHomologicalComplex (.up ℕ)).map (Bounded.RelativeSheafComplex.augmentation w n FI))
      (CechGeometricTotal.iso p k n X Y f hp I).hom (frameRestrictionIso p k n X Y f hp I).hom
      (((L).mapHomologicalComplex (.up ℕ)).map (GeometricComparison.Semilattice.ChartTotal.SemilatticeChartTotal.map X.left.affineOpens U I P H))
      (sheaf_factorization p k n X Y f hp I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechChartAugmentation
