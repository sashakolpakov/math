import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechResolutionLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.SquareIsoTransport

/-! # Diagonal Cech Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel

noncomputable section

/-! The original native diagonal-section to sheafified-Cech comparison
commutes with the actual bounded-level maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n m hnm
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram.transformation p X Y f hp n m hnm
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap.IntrinsicPadicSectionLevelMap.transformation p X Y f n m hnm
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X

local instance sheafCoproducts (q : ℕ) : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap q) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (IntegralComparison.BoundedCrystalline.Site.topology wittMap q)

def diagonalMap : PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.source p X Y f hp m ⟶
    PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.source p X Y f hp n :=
  Section.DiagonalConeChange.SectionDiagonalConeChange.diagonalMap X.left.affineOpens T (S m) (S n) (P m) (P n) a b

def sectionsMap : ((S m).mapHomologicalComplex (.up ℕ)).obj (K m) ⟶
    ((S n).mapHomologicalComplex (.up ℕ)).obj (K n) :=
  ((b).mapHomologicalComplex (.up ℕ)).app (K m) ≫
    ((S n).mapHomologicalComplex (.up ℕ)).map (CechResolutionLevel.IntrinsicPadicCechResolutionLevel.map p X Y f hp n m hnm)

def totalSectionsMap : ((S m).mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U (P m)) ⟶
    ((S n).mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U (P n)) :=
  ((b).mapHomologicalComplex (.up ℕ)).app (CechCone.Total.CechConeTotal.total U (P m)) ≫
    ((S n).mapHomologicalComplex (.up ℕ)).map
      (CechResolutionLevel.IntrinsicPadicCechResolutionLevel.diagramMap p X Y f hp n m hnm)

theorem canonical_natural : Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens R (S m) (P m)
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp m) U ≫ totalSectionsMap p X Y f hp n m hnm =
  diagonalMap p X Y f hp n m hnm ≫ Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens R (S n) (P n)
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp n) U :=
  Section.DiagonalCechChange.SectionDiagonalCechChange.natural.{0, 2, 1, 2, 1, 1, 2} X.left.affineOpens R T (S m) (S n) (P m) (P n) a b
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp m)
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp n) U

theorem isomorphism_square : ((S m).mapHomologicalComplex (.up ℕ)).map
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp m).inv ≫ sectionsMap p X Y f hp n m hnm =
      totalSectionsMap p X Y f hp n m hnm ≫ ((S n).mapHomologicalComplex (.up ℕ)).map
        (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).inv :=
  Functor.SquareIsoTransport.FunctorSquareIsoTransport.square ((T).mapHomologicalComplex (.up ℕ))
    ((S m).mapHomologicalComplex (.up ℕ)) ((S n).mapHomologicalComplex (.up ℕ))
    ((b).mapHomologicalComplex (.up ℕ)) (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp m)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n)
    (CechResolutionLevel.IntrinsicPadicCechResolutionLevel.diagramMap p X Y f hp n m hnm)

theorem natural : PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp m ≫ sectionsMap p X Y f hp n m hnm =
    diagonalMap p X Y f hp n m hnm ≫ PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp n :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens R (S m) (P m)
      (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp m) U ≫ q)
      (isomorphism_square p X Y f hp n m hnm)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ ((S n).mapHomologicalComplex (.up ℕ)).map
            (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).inv)
            (canonical_natural p X Y f hp n m hnm)).trans (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCechLevel.IntrinsicPadicDiagonalCechLevel
