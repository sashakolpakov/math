import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction

/-! # Frobenius Global Open Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusGlobalOpenMap.LevelZeroFrobeniusGlobalOpenMap

noncomputable section

/-! Original global-to-open section restriction commutes with the
actual level-zero crystalline Frobenius restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))

local notation "W" => WittVector p (ZMod p)
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.postcompose p Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0

local instance continuous : (G).IsContinuous (IntegralComparison.BoundedCrystalline.Site.topology w 0) (IntegralComparison.BoundedCrystalline.Site.topology w 0) :=
  IntegralComparison.Bounded.PostcomposeTopology.continuous g hg 0

def restriction : Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0 ⟶
      R ⋙ Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections w 0 :=
  IntegralComparison.Sheaf.PresheafSectionRestriction.map G Rcoeff (IntegralComparison.BoundedCrystalline.Site.topology w 0) (IntegralComparison.BoundedCrystalline.Site.topology w 0)

theorem natural : Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0 ≫
      FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y =
    Functor.whiskerRight (restriction p Y) (Functor.const Y.left.Opensᵒᵖ) ≫
      Functor.whiskerLeft R (Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w 0) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusGlobalOpenMap.LevelZeroFrobeniusGlobalOpenMap
