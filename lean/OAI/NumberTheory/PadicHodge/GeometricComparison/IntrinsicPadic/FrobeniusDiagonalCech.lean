import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusCechResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.SquareIsoTransport
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSectionMap

/-! # Frobenius Diagonal Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech

noncomputable section

/-! The original native diagonal-section to sheafified-Cech comparison
commutes with the actual level-zero Frobenius maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "W" => WittVector p (ZMod p)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram.transformation p X Y f hp
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap.transformation p X Y f
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X

local instance sheafCoproducts (q : ℕ) : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap q) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (IntegralComparison.BoundedCrystalline.Site.topology wittMap q)

def diagonalMap : PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.source p X Y f hp 0 ⟶
    PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.source p X Y f hp 0 :=
  Section.DiagonalConeChange.SectionDiagonalConeChange.diagonalMap X.left.affineOpens T (S 0) (S 0) (P 0) (P 0) a b

def sectionsMap : ((S 0).mapHomologicalComplex (.up ℕ)).obj (K 0) ⟶
    ((S 0).mapHomologicalComplex (.up ℕ)).obj (K 0) :=
  Section.CochainPullback.SectionCochainPullback.map T (S 0) (S 0) b
    (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.map p X Y f hp)

def totalSectionsMap : ((S 0).mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U (P 0)) ⟶
    ((S 0).mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U (P 0)) :=
  CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map T (S 0) (S 0) U (P 0) (P 0) a b

theorem canonical_natural : Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens R (S 0) (P 0)
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp 0) U ≫ totalSectionsMap p X Y f hp =
  diagonalMap p X Y f hp ≫ Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens R (S 0) (P 0)
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp 0) U :=
  Section.DiagonalCechChange.SectionDiagonalCechChange.natural.{0, 2, 1, 2, 1, 1, 2} X.left.affineOpens R T (S 0) (S 0) (P 0) (P 0) a b
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp 0)
    (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp 0) U

theorem totalSectionsMap_eq : totalSectionsMap p X Y f hp =
    Section.CochainPullback.SectionCochainPullback.map T (S 0) (S 0) b
      (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.diagramMap p X Y f hp) :=
  CechCone.TotalSectionMap.CechConeTotalSectionMap.map_eq T (S 0) (S 0) U (P 0) (P 0) a b

theorem raw_isomorphism_square : ((S 0).mapHomologicalComplex (.up ℕ)).map
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv ≫ sectionsMap p X Y f hp =
      Section.CochainPullback.SectionCochainPullback.map T (S 0) (S 0) b
        (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.diagramMap p X Y f hp) ≫ ((S 0).mapHomologicalComplex (.up ℕ)).map
        (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv :=
  Functor.SquareIsoTransport.FunctorSquareIsoTransport.square ((T).mapHomologicalComplex (.up ℕ))
    ((S 0).mapHomologicalComplex (.up ℕ)) ((S 0).mapHomologicalComplex (.up ℕ))
    ((b).mapHomologicalComplex (.up ℕ)) (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0)
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0)
    (FrobeniusCechResolution.IntrinsicPadicFrobeniusCechResolution.diagramMap p X Y f hp)

theorem isomorphism_square : ((S 0).mapHomologicalComplex (.up ℕ)).map
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv ≫ sectionsMap p X Y f hp =
      totalSectionsMap p X Y f hp ≫ ((S 0).mapHomologicalComplex (.up ℕ)).map
        (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv :=
  (raw_isomorphism_square p X Y f hp).trans
    (congrArg (fun q => q ≫ ((S 0).mapHomologicalComplex (.up ℕ)).map
      (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv)
        (totalSectionsMap_eq p X Y f hp).symm)

theorem natural : PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp 0 ≫ sectionsMap p X Y f hp =
    diagonalMap p X Y f hp ≫ PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalMap p X Y f hp 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => Section.DiagonalCech.SectionDiagonalCechComparison.map.{0, 2, 1, 1, 2} X.left.affineOpens R (S 0) (P 0)
      (SectionRowRestriction.IntrinsicPadicSectionRowRestriction.meet_isIso p X Y f hp 0) U ≫ q)
      (isomorphism_square p X Y f hp)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ ((S 0).mapHomologicalComplex (.up ℕ)).map
            (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp 0).inv)
            (canonical_natural p X Y f hp)).trans (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusDiagonalCech.IntrinsicPadicFrobeniusDiagonalCech
