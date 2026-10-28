import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionLevelDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange

/-! # Section Level Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap.IntrinsicPadicSectionLevelMap

noncomputable section

/-! Original native open-section restriction and native frame-level maps
give the actual level transformation of the section bifunctors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n m hnm
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f

def transformation : S m ⟶ T ⋙ S n :=
  Functor.whiskerRight (Bounded.OpenSectionLevel.BoundedOpenSectionLevel.transformation wittMap n m hnm)
    ((Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} R)).obj
      (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f).op)

variable (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp

def complexes : P m ⋙ (S m).mapHomologicalComplex (.up ℕ) ⟶ P n ⋙ (S n).mapHomologicalComplex (.up ℕ) :=
  Section.ComplexBifunctorChange.SectionComplexBifunctorChange.complexes T (S m) (S n) (P m) (P n)
    (ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram.transformation p X Y f hp n m hnm)
    (transformation p X Y f n m hnm)

def rows : SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp m ⟶ SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp n :=
  Section.ComplexBifunctorChange.SectionComplexBifunctorChange.rows T (S m) (S n) (P m) (P n)
    (ResolutionLevelDiagram.IntrinsicPadicResolutionLevelDiagram.transformation p X Y f hp n m hnm)
    (transformation p X Y f n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap.IntrinsicPadicSectionLevelMap
