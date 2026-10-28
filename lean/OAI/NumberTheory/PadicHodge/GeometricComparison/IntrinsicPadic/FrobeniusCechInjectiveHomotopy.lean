import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusCechResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedNaturality

/-! # Frobenius Cech Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusCechInjectiveHomotopy.IntrinsicPadicFrobeniusCechInjectiveHomotopy

noncomputable section

/-! The full native Cech-to-injective comparison commutes up to homotopy
with actual level-zero crystalline Frobenius. -/

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

local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg 0
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp 0
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp 0

def homotopy : Homotopy
    (((R).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I) ≫
      ExactInjective.ExactInjectivePullback.map R e I I)
    (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.map p X Y f hp ≫
      CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I) :=
  AugmentedNaturality.AugmentedComparisonNaturality.homotopy R e
    K a (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation_quasiIso p X Y f hp 0)
    K a (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation_quasiIso p X Y f hp 0)
    I I (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.map p X Y f hp)
    (ExactInjective.ExactInjectivePullback.map R e I I)
    (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.augmentation p X Y f hp)
    (ExactInjective.ExactInjectivePullback.augmentation_map R e I I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusCechInjectiveHomotopy.IntrinsicPadicFrobeniusCechInjectiveHomotopy
