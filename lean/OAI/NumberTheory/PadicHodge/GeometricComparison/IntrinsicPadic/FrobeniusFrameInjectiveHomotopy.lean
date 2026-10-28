import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameDiagonal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyPrecomposition

/-! # Frobenius Frame Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameInjectiveHomotopy.IntrinsicPadicFrobeniusFrameInjectiveHomotopy

noncomputable section

/-! The original native frame-to-injective comparison respects actual
level-zero Frobenius up to cochain homotopy on actual open sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0))

local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def homotopy : Homotopy
    (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp 0 I ≫
      FrobeniusDiagonalInjectiveHomotopy.IntrinsicPadicFrobeniusDiagonalInjectiveHomotopy.injectiveMap p X Y f I)
    (FrobeniusFrameDiagonal.IntrinsicPadicFrobeniusFrameDiagonal.map p X Y f hp ≫
      FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp 0 I) :=
  HomotopyPrecomposition.HomotopyPrecompositionSquare.homotopy
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp 0)
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp 0)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp 0 I)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp 0 I)
    (FrobeniusDiagonalInjectiveHomotopy.IntrinsicPadicFrobeniusDiagonalInjectiveHomotopy.injectiveMap p X Y f I)
    (FrobeniusFrameDiagonal.IntrinsicPadicFrobeniusFrameDiagonal.map p X Y f hp)
    (FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech.diagonalMap p X Y f hp)
    (FrobeniusDiagonalInjectiveHomotopy.IntrinsicPadicFrobeniusDiagonalInjectiveHomotopy.homotopy p X Y f hp I)
    (FrobeniusFrameDiagonal.IntrinsicPadicFrobeniusFrameDiagonal.natural p X Y f hp)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameInjectiveHomotopy.IntrinsicPadicFrobeniusFrameInjectiveHomotopy
