import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalInjectiveLevelHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyPrecomposition

/-! # Frame Injective Level Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjectiveLevelHomotopy.IntrinsicPadicFrameInjectiveLevelHomotopy

noncomputable section

/-! The original native frame-to-injective comparison respects bounded
levels up to cochain homotopy on actual open sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap m I

def homotopy : Homotopy
    (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp m Im ≫
      DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy.injectiveMap p X Y f n m hnm I)
    (FrameDiagonalLevel.IntrinsicPadicFrameDiagonalLevel.map p X Y f hp n m hnm ≫
      FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp n In) :=
  HomotopyPrecomposition.HomotopyPrecompositionSquare.homotopy
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp m)
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp n)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp m Im)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp n In)
    (DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy.injectiveMap p X Y f n m hnm I)
    (FrameDiagonalLevel.IntrinsicPadicFrameDiagonalLevel.map p X Y f hp n m hnm)
    (DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel.diagonalMap p X Y f hp n m hnm)
    (DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy.homotopy p X Y f hp n m hnm I)
    (FrameDiagonalLevel.IntrinsicPadicFrameDiagonalLevel.natural p X Y f hp n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjectiveLevelHomotopy.IntrinsicPadicFrameInjectiveLevelHomotopy
