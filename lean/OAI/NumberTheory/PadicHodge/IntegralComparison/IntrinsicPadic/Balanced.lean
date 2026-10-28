import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicBijective

/-! # Balanced -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.Balanced.IntrinsicComparison

noncomputable section

/-! The original Ext comparison for the genuine finite-level model
resolution is a linear equivalence on its bounded-frame Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "m" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech.IntrinsicComparison.frames p X Y f hp n
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n
local notation "cover" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n

abbrev comparison (i : ℕ) :=
  Balanced.IntrinsicFrameAugmentation.Intrinsic.comparison.{1,0,2} F Rcoeff JT cover J K m i

theorem bijective (i : ℕ) : Function.Bijective (comparison p X Y f hp n J i) := by
  let : QuasiIso (Balanced.IntrinsicBijective.IntrinsicComparison.totalMap F Rcoeff JT J K m) :=
    BoundedCech.IntrinsicComparison.quasiIso p X Y f hp n J
  exact Balanced.IntrinsicBijective.IntrinsicComparison.bijective.{1,0,2} F Rcoeff JT cover J K m i

noncomputable def equivalence (i : ℕ) :=
  LinearEquiv.ofBijective (comparison p X Y f hp n J i)
    (bijective p X Y f hp n J i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.Balanced.IntrinsicComparison
