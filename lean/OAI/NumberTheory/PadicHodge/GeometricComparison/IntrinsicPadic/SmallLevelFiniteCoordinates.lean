import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralLevelGlobalCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallGlobalLevel

/-! # Small Level Finite Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallLevelFiniteCoordinates.IntrinsicPadicSmallLevelFiniteCoordinates

noncomputable section

/-! The actual small-coefficient level comparison agrees with its
original finite integral comparison at the restricted resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y))) (n : ℕ)

local notation "Iq" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n I

def finiteIso := SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n ≪≫
  IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X Y f hp n Iq

theorem homology : (SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel.iso p X Y f hp I n).hom =
    (finiteIso p X Y f hp I n).hom :=
  congrArg (fun a => (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n).hom ≫ a)
    (IntegralLevelGlobalCoordinates.IntrinsicPadicIntegralLevelGlobalCoordinates.homology p X Y f hp I n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallLevelFiniteCoordinates.IntrinsicPadicSmallLevelFiniteCoordinates
