import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechResolutionLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Resolution

/-! # Cech Injective Level Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjectiveLevelHomotopy.IntrinsicPadicCechInjectiveLevelHomotopy

noncomputable section

/-! The original native global Cech-to-injective comparisons commute
with bounded-level restriction up to a canonical comparison homotopy. -/

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

local notation "W" => WittVector p (ZMod p)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n m hnm
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp

def homotopy := AugmentedNaturality.AugmentedComparisonNaturality.homotopy T
  (IntegralComparison.Bounded.CohomologyTransition.structureIso wittMap n m hnm)
  (K m) (a m) (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation_quasiIso p X Y f hp m)
  (K n) (a n) (CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation_quasiIso p X Y f hp n)
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap m I)
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap n I)
  (CechResolutionLevel.IntrinsicPadicCechResolutionLevel.map p X Y f hp n m hnm)
  (IntegralComparison.BoundedLevel.Resolution.cocomplexIso wittMap n m hnm I).hom
  (CechResolutionLevel.IntrinsicPadicCechResolutionLevel.augmentation p X Y f hp n m hnm)
  (IntegralComparison.BoundedLevel.Resolution.augmentation wittMap n m hnm I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjectiveLevelHomotopy.IntrinsicPadicCechInjectiveLevelHomotopy
