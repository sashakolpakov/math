import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCechLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjectiveLevelHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.HomotopySquare

/-! # Diagonal Injective Level Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy

noncomputable section

/-! The original native diagonal-to-injective section comparisons
commute with bounded-level restriction up to cochain homotopy. -/

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
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap m I
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap.IntrinsicPadicSectionLevelMap.transformation p X Y f n m hnm

def injectiveMap := ((b).mapHomologicalComplex (.up ℕ)).app (Im).cocomplex ≫
  ((S n).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedLevel.Resolution.cocomplexIso wittMap n m hnm I).hom

def homotopyCore : Homotopy
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp m Im ≫ injectiveMap p X Y f n m hnm I)
    ((DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel.diagonalMap p X Y f hp n m hnm ≫
      PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp n) ≫
        ((S n).mapHomologicalComplex (.up ℕ)).map (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n In)) :=
  Section.HomotopySquare.SectionComparisonHomotopySquare.homotopy T (S m) (S n) b
  (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp m Im)
  (CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n In)
  (CechResolutionLevel.IntrinsicPadicCechResolutionLevel.map p X Y f hp n m hnm)
  (IntegralComparison.BoundedLevel.Resolution.cocomplexIso wittMap n m hnm I).hom
  (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp m)
  (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp n)
  (DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel.diagonalMap p X Y f hp n m hnm)
  (CechInjectiveLevelHomotopy.IntrinsicPadicCechInjectiveLevelHomotopy.homotopy p X Y f hp n m hnm I)
  (DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel.natural p X Y f hp n m hnm)

def homotopy : Homotopy
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp m Im ≫ injectiveMap p X Y f n m hnm I)
    (DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel.diagonalMap p X Y f hp n m hnm ≫
      PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp n In) :=
  (homotopyCore p X Y f hp n m hnm I).trans (Homotopy.ofEq (Category.assoc _ _ _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy
