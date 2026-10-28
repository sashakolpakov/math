import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback

/-! # Frobenius Injective Section Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap

noncomputable section

/-! The original native injective-section Frobenius map, with its
source and target complexes named independently of comparison homotopies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0))

local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg 0
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f 0

def map : ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  Section.CochainPullback.SectionCochainPullback.map T S S (FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap.transformation p X Y f)
    (ExactInjective.ExactInjectivePullback.map T e I I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap
