import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.GlobalSectionQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSourceQuasiIso

/-! # Frame Section Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionQuasiIso.Intrinsic

noncomputable section

/-! The literal normalized section map of the actual p-adic frame is a
quasi-isomorphism, through its original sheaf and source coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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

abbrev quasiIso :=
  (Balanced.SheafifiedSourceQuasiIso.Coordinates.quasiIso_iff.{1,2} CR JT I M P a m
    (FrameSectionCoordinates.Intrinsic.sourceTotal p X Y f hp n)
    (FrameSectionCoordinates.Intrinsic.targetTotal p X Y f hp n)
    (FrameSourceCoordinates.Intrinsic.sourceIso p X Y f hp n)
    (GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n)
    (FrameSectionCoordinates.Intrinsic.levelMap p X Y f hp n)
    (FrameSectionCoordinates.Intrinsic.sheaf_square p X Y f hp n)).mpr
    (GlobalSectionQuasiIso.IntrinsicFrame.quasiIso p X Y f hp n I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionQuasiIso.Intrinsic
