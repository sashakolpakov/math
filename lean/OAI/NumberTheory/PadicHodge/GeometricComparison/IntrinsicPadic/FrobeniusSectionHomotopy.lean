import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusCechInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.PullbackHomotopy

/-! # Frobenius Section Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionHomotopy.IntrinsicPadicFrobeniusSectionComparisonHomotopy

noncomputable section

/-! Actual Frobenius compatibility of the native section comparison,
with diagonal precomposition kept separate. -/

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

local notation "W" => WittVector p (ZMod p)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg 0
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap.transformation p X Y f

def homotopy : Homotopy
    (((S 0).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I) ≫
      FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap.map p X Y f I)
    (FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech.sectionsMap p X Y f hp ≫
      ((S 0).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I)) :=
  Section.PullbackHomotopy.SectionPullbackHomotopy.homotopy T (S 0) (S 0) b
    (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I)
    (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I)
    (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.map p X Y f hp)
    (ExactInjective.ExactInjectivePullback.map T e I I)
    (FrobeniusCechInjectiveHomotopy.IntrinsicPadicFrobeniusCechInjectiveHomotopy.homotopy p X Y f hp I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionHomotopy.IntrinsicPadicFrobeniusSectionComparisonHomotopy
