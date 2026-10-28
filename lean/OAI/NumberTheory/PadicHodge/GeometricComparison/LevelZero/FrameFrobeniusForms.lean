import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicPD
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ChangeNaturality

/-! # Frame Frobenius Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusForms.LevelZeroFrameFrobeniusForms

noncomputable section

/-! The actual level-zero Frobenius frame map kills every original
positive-degree divided-power differential form. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))
  (U : IntegralComparison.BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "V" => Functor.obj (OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.postcompose p Y) U
local notation "α" => InducedCategory.Hom.hom (OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y U)

theorem positive (n : ℕ) (hn : 0 < n) :
    (IntegralComparison.RelativeFrame.ChangeNaturality.frameMap U.obj (V).obj α).f n = 0 := by
  let : Algebra (WittVector p (ZMod p)) U.obj.ring := U.obj.base.toAlgebra
  let : Algebra (WittVector p (ZMod p)) (V).obj.ring := (V).obj.base.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact CharacteristicPD.CharacteristicPDFormPullback.power_zero
    (CommAlgCat.ofHom (IntegralComparison.Crystalline.DeRham.ambientMap w α))
    (IntegralComparison.Crystalline.DeRham.ambientMap_isDPMorphism w α) p
    (CrystallineFrobenius.LevelZeroCrystallineFrobenius.prime_zero p Y U) (fun x => ⟨x, rfl⟩) n hn ω

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusForms.LevelZeroFrameFrobeniusForms
