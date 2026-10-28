import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjectiveLevelHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSourceAssemblyLevel

/-! # Integral Injective Level Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveLevelHomotopy.IntrinsicPadicIntegralInjectiveLevelHomotopy

noncomputable section

/-! The canonical integral quotient-to-injective comparison commutes
with original bounded levels up to cochain homotopy. -/

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
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp m Im ≫
      DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy.injectiveMap p X Y f n m hnm I)
    (IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceAssemblyLevel.map p X n m hnm ≫
      IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n In) :=
  HomotopyPrecomposition.HomotopyPrecompositionSquare.homotopy
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp m))
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp n))
    (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp m Im)
    (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp n In)
    (DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy.injectiveMap p X Y f n m hnm I)
    (IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceAssemblyLevel.map p X n m hnm)
    (FrameDiagonalLevel.IntrinsicPadicFrameDiagonalLevel.map p X Y f hp n m hnm)
    (FrameInjectiveLevelHomotopy.IntrinsicPadicFrameInjectiveLevelHomotopy.homotopy p X Y f hp n m hnm I)
    (IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceAssemblyLevel.natural p X Y f hp n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveLevelHomotopy.IntrinsicPadicIntegralInjectiveLevelHomotopy
