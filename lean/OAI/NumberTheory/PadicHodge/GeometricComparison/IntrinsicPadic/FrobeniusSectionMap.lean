import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusResolutionDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange

/-! # Frobenius Section Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap

noncomputable section

/-! Actual level-zero Frobenius acts on the original native section
bifunctor, with the full frame resolution and actual open-section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f 0

def transformation : S ⟶ R ⋙ S :=
  Functor.whiskerRight (LevelZero.FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y)
    ((Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} Rcoeff)).obj
      (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f).op)

variable (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp 0

def complexes : P ⋙ (S).mapHomologicalComplex (.up ℕ) ⟶ P ⋙ (S).mapHomologicalComplex (.up ℕ) :=
  Section.ComplexBifunctorChange.SectionComplexBifunctorChange.complexes R S S P P
    (FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram.transformation p X Y f hp)
    (transformation p X Y f)

def rows : SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp 0 ⟶ SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp 0 :=
  Section.ComplexBifunctorChange.SectionComplexBifunctorChange.rows R S S P P
    (FrobeniusResolutionDiagram.IntrinsicPadicFrobeniusResolutionDiagram.transformation p X Y f hp)
    (transformation p X Y f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap
