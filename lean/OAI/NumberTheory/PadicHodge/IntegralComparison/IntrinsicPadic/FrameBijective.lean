import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameConeQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedBijective
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameCohomologyProduct

/-! # Frame Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameBijective.IntrinsicComparison

noncomputable section

/-! The original p-adic frame product comparison with bounded crystalline
cohomology is bijective by its exact injective-section normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech.IntrinsicComparison.frames p X Y f hp n
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic.coefficientSource p X Y f hp n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic.coefficientComplex p X Y f hp n
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic.coefficientMap p X Y f hp n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf
      (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts CR JT

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "m" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I

abbrev sections_quasiIso :=
  FrameConeQuasiIso.Intrinsic.quasiIso p X Y f hp n I

theorem bijective (i : ℕ) : Function.Bijective
    ((Lifted.AugmentationTransport.comparison
      (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{1,0,2} F CR JT
        (Sheafified.ConstantCochainCoordinates.sheafComplex CR JT P)) i
      (Balanced.FrameAugmentation.comparison F CR JT
        (GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n) I
        (Sheafified.ConstantCochainCoordinates.sheafComplex CR JT P) m i).hom).comp
      (HomologicalComplex.homologyMap (Sheafified.ConstantCechMap.map F CR JT M P a) i).hom) := Balanced.SheafifiedBijective.Comparison.bijective.{1,2}
  F CR JT (GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n) I M P a m
  (sections_quasiIso p X Y f hp n I) i

omit I in
theorem comparison_bijective (i : ℕ) :
    Function.Bijective (FrameCohomologyProduct.Intrinsic.comparison p X Y f hp n i) :=
  bijective p X Y f hp n (BalancedBounded.CechCup.resolution p (ZMod p) w n) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameBijective.IntrinsicComparison
