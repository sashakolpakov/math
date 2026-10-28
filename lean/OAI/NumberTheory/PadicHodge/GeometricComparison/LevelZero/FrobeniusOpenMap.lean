import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionFunctorMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex

/-! # Frobenius Open Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusOpenMap.LevelZeroFrobeniusOpenMap

noncomputable section

/-! The actual level-zero crystalline Frobenius preserves every open
subsite and acts naturally on its original Zariski section functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))

local notation "W" => WittVector p (ZMod p)
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.postcompose p Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.property (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.functor (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0

theorem preserves (U : Y.left.Opens) (A : IntegralComparison.BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0) : P U A → P U ((G).obj A) :=
  IntegralComparison.BoundedOpen.SectionPresheaf.incoming w 0 U (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y A)

def sectionMap (I : IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0) : (S).obj I ⟶ (S).obj ((R).obj I) :=
  IntegralComparison.Incoming.SectionFunctorMap.presheafMap G Rcoeff (ModuleCat.of Rcoeff Rcoeff) P P
    (IntegralComparison.BoundedOpen.SectionPresheaf.monotone w 0) (IntegralComparison.BoundedOpen.SectionPresheaf.monotone w 0)
    (preserves p Y) I.obj

def functorMap : S ⟶ R ⋙ S where
  app I := sectionMap p Y I
  naturality _ _ a :=
    (IntegralComparison.Incoming.SectionFunctorMap.functorMap G Rcoeff (ModuleCat.of Rcoeff Rcoeff) P P
      (IntegralComparison.BoundedOpen.SectionPresheaf.monotone w 0) (IntegralComparison.BoundedOpen.SectionPresheaf.monotone w 0)
      (preserves p Y)).naturality a.hom

def largeFunctorMap : IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0 ⟶
      R ⋙ IntegralComparison.BoundedOpen.SectionComplex.functor w 0 :=
  Functor.whiskerRight (functorMap p Y)
    ((Functor.whiskeringRight Y.left.Opensᵒᵖ (ModuleCat.{1} Rcoeff) (ModuleCat.{2} Rcoeff)).obj
      (ModuleCat.uliftFunctor.{2, 1} Rcoeff))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusOpenMap.LevelZeroFrobeniusOpenMap
