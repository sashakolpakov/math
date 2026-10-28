import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram

/-! # Frobenius Resolution Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram

noncomputable section

/-! Actual level-zero Frobenius acts on the full native frame-resolution
diagram and preserves the original crystalline structure augmentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp 0

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def transformation : P ⋙ (R).mapHomologicalComplex (.up ℕ) ⟶ P :=
  Functor.whiskerLeft (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp 0).op
    (LevelZero.FrameFrobeniusSheaf.LevelZeroFrameFrobeniusSheaf.transformation p Y)

theorem augmentation (U : X.left.affineOpens) :
    IntegralComparison.Single.ComplexTransport.map R (IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg 0)
      ((PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp 0).app (op U)) ≫
        (transformation p X Y f hp).app (op U) =
      (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp 0).app (op U) :=
  LevelZero.FrameFrobeniusSheaf.LevelZeroFrameFrobeniusSheaf.augmentation p Y
    ((FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp 0).obj U)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram
