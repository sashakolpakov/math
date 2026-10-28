import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelSheafNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelSheafDiagramMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram

/-! # Resolution Level Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram

noncomputable section

/-! Canonical native frame reduction assembles into a natural map between
the original relative sheaf-resolution diagrams at bounded levels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n m hnm
local notation "TG" => Functor.mapHomologicalComplex T (ComplexShape.up ℕ)
local notation "frame" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp

local instance separated : IsSeparated wittMap := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def transformation : P m ⋙ TG ⟶ P n :=
  Bounded.LevelSheafDiagramMap.BoundedLevelSheafDiagramMap.transformation wittMap n m hnm (frame n) (frame m)
    (FrameLevelNaturality.IntrinsicPadicFrameLevelNaturality.transformation p X Y f hp n m hnm)

theorem app_eq (U : X.left.affineOpens) :
    (transformation p X Y f hp n m hnm).app (op U) =
      IntegralComparison.BoundedLevel.FrameMap.map wittMap n m hnm
        (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U.val U.property n m hnm) :=
  Bounded.LevelSheafDiagramMap.BoundedLevelSheafDiagramMap.app_eq wittMap n m hnm (frame n) (frame m)
    (FrameLevelNaturality.IntrinsicPadicFrameLevelNaturality.transformation p X Y f hp n m hnm) U

theorem augmentation (U : X.left.affineOpens) :
    IntegralComparison.Single.ComplexTransport.map T (IntegralComparison.Bounded.CohomologyTransition.structureIso wittMap n m hnm)
      ((PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp m).app (op U)) ≫
        (transformation p X Y f hp n m hnm).app (op U) =
      (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp n).app (op U) :=
  Bounded.LevelSheafDiagramMap.BoundedLevelSheafDiagramMap.augmentation wittMap n m hnm (frame n) (frame m)
    (FrameLevelNaturality.IntrinsicPadicFrameLevelNaturality.transformation p X Y f hp n m hnm) U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram
