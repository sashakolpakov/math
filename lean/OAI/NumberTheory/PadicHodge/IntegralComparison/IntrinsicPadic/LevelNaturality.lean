import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechLevel
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare

/-! # Level Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.LevelNaturality.IntrinsicIntegral

noncomputable section

/-! The existing native finite p-adic comparison commutes with its
original level transitions in every cohomological degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2,0,0} R E (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I m)) i ≫
    HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2,0,0} R E (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm)) i =
      HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2,0,0} R E (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.sourceMap p X n m hnm)) i ≫
        HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2,0,0} R E (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n)) i := AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare.CechTotalHomotopySquare.homology.{1,2,0,0} R E
  (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I m)
  (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm)
  (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.sourceMap p X n m hnm)
  (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n)
  (GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.homotopy p X Y f hp I n m hnm) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.LevelNaturality.IntrinsicIntegral
