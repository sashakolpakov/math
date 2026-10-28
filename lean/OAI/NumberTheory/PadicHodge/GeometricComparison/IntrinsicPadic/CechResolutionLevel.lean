import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionLevelDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafAugmentationCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap

/-! # Cech Resolution Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechResolutionLevel.IntrinsicPadicCechResolutionLevel

noncomputable section

/-! Canonical bounded-level reduction maps the actual native global Cech
resolutions and preserves their original crystalline augmentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n m hnm
local notation "TG" => Functor.mapHomologicalComplex T (ComplexShape.up ℕ)
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "structureIso" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.structureIso (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n m hnm

local instance separated : IsSeparated wittMap := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts (q : ℕ) : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap q) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
    (IntegralComparison.BoundedCrystalline.Site.topology wittMap q)

def diagramMap : (TG).obj (CechCone.Total.CechConeTotal.total U (P m)) ⟶ CechCone.Total.CechConeTotal.total U (P n) :=
  CechCone.TotalLevelMap.CechConeTotalLevelMap.map T U (P m) (P n)
    (ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram.transformation p X Y f hp n m hnm)

def diagramAugmentation (q : ℕ) := CechCone.Total.CechConeTotal.augmentation U (P q) _
  (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp q)

theorem diagram_augmentation : IntegralComparison.Single.ComplexTransport.map T structureIso
    (diagramAugmentation p X Y f hp m) ≫ diagramMap p X Y f hp n m hnm =
      diagramAugmentation p X Y f hp n :=
  CechCone.TotalLevelMap.CechConeTotalLevelMap.augmentation T U (P m) (P n)
    (ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram.transformation p X Y f hp n m hnm) structureIso
    (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp m)
    (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp n)
    (fun V => ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram.augmentation p X Y f hp n m hnm V.unop)

def map : (TG).obj (CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp m) ⟶
    CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n :=
  (TG).map (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp m).hom ≫
    diagramMap p X Y f hp n m hnm ≫ (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).inv

theorem augmentation : IntegralComparison.Single.ComplexTransport.map T structureIso
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp m) ≫ IntrinsicPadicCechResolutionLevel.map p X Y f hp n m hnm =
      CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n := by
  have h₁ := (IntegralComparison.Single.ComplexTransportNaturality.comp T structureIso
    (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp m)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp m).hom).trans
      (congrArg (IntegralComparison.Single.ComplexTransport.map T structureIso)
        (CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates.augmentation p X Y f hp m))
  have h₂ := diagram_augmentation p X Y f hp n m hnm
  have h₃ := (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).comp_inv_eq.mpr
    (CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates.augmentation p X Y f hp n).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ diagramMap p X Y f hp n m hnm ≫
      (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).inv) h₁).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).inv) h₂).trans h₃)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechResolutionLevel.IntrinsicPadicCechResolutionLevel
