import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange

/-! # Frame Frobenius Coefficient Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusCoefficientForms.LevelZeroFrameFrobeniusCoefficientForms

noncomputable section

/-! Vanishing of positive-degree frame Frobenius persists through the
actual crystalline coefficient transport and universe lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (U : IntegralComparison.BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "V" => Functor.obj (OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.postcompose p Y) U
local notation "α" => InducedCategory.Hom.hom (OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y U)

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

omit [IsSeparated Y.hom] in
theorem positive (n : ℕ) (hn : 0 < n) :
    (ModuleCat.uliftFunctor.{2, 1} R).map
      ((IntegralComparison.BoundedFrame.SectionChange.frameMap (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y U)).f n) = 0 := by
  change (ModuleCat.uliftFunctor.{2, 1} R).map
    ((IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := WittVector p (ZMod p))).map
      ((IntegralComparison.RelativeFrame.ChangeNaturality.frameMap U.obj (V).obj α).f n)) = 0
  rw [FrameFrobeniusForms.LevelZeroFrameFrobeniusForms.positive p Y U n hn, Functor.map_zero, Functor.map_zero]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusCoefficientForms.LevelZeroFrameFrobeniusCoefficientForms
