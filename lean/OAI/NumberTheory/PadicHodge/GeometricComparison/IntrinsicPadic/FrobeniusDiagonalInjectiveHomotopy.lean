import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyPrecomposition

/-! # Frobenius Diagonal Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalInjectiveHomotopy.IntrinsicPadicFrobeniusDiagonalInjectiveHomotopy

noncomputable section

/-! The original native diagonal-to-injective section comparisons
commute with actual level-zero Frobenius up to cochain homotopy. -/

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

abbrev injectiveMap := FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap.map p X Y f I

def homotopy : Homotopy
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp 0 I ≫ injectiveMap p X Y f I)
    (FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech.diagonalMap p X Y f hp ≫
      PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp 0 I) :=
  HomotopyPrecomposition.HomotopyPrecompositionSquare.homotopy
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp 0)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp 0)
    (((S 0).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I))
    (((S 0).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp 0 I))
    (injectiveMap p X Y f I)
    (FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech.diagonalMap p X Y f hp)
    (FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech.sectionsMap p X Y f hp)
    (FrobeniusSectionHomotopy.IntrinsicPadicFrobeniusSectionComparisonHomotopy.homotopy p X Y f hp I)
    (FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech.natural p X Y f hp)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalInjectiveHomotopy.IntrinsicPadicFrobeniusDiagonalInjectiveHomotopy
