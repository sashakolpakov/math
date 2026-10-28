import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusResolutionDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafAugmentationCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap

/-! # Frobenius Cech Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution

noncomputable section

/-! Actual level-zero Frobenius maps the full native crystalline Cech
resolution to itself and preserves its original structure augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "RH" => Functor.mapHomologicalComplex R (ComplexShape.up ℕ)
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp 0
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg 0

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
    (IntegralComparison.BoundedCrystalline.Site.topology w 0)

def diagramMap : (RH).obj (CechCone.Total.CechConeTotal.total U P) ⟶ CechCone.Total.CechConeTotal.total U P :=
  CechCone.TotalLevelMap.CechConeTotalLevelMap.map R U P P (FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram.transformation p X Y f hp)

def diagramAugmentation := CechCone.Total.CechConeTotal.augmentation U P _
  (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp 0)

theorem diagram_augmentation : IntegralComparison.Single.ComplexTransport.map R e (diagramAugmentation p X Y f hp) ≫
    diagramMap p X Y f hp = diagramAugmentation p X Y f hp :=
  CechCone.TotalLevelMap.CechConeTotalLevelMap.augmentation R U P P
    (FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram.transformation p X Y f hp) e
    (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp 0)
    (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp 0)
    (fun V => FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram.augmentation p X Y f hp V.unop)

def map : (RH).obj (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp 0) ⟶
    CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp 0 :=
  (RH).map (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).hom ≫
    diagramMap p X Y f hp ≫ (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv

theorem augmentation : IntegralComparison.Single.ComplexTransport.map R e
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp 0) ≫ IntrinsicPadicFrobeniusCechResolution.map p X Y f hp =
      CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp 0 := by
  have h₁ := (IntegralComparison.Single.ComplexTransportNaturality.comp R e
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp 0)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).hom).trans
      (congrArg (IntegralComparison.Single.ComplexTransport.map R e)
        (CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates.augmentation p X Y f hp 0))
  have h₂ := diagram_augmentation p X Y f hp
  have h₃ := (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).comp_inv_eq.mpr
    (CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates.augmentation p X Y f hp 0).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ diagramMap p X Y f hp ≫
      (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv) h₁).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv) h₂).trans h₃)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution
