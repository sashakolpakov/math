import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.Balanced
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.Augmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicativeDescent

/-! # Balanced Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BalancedProduct.Intrinsic

noncomputable section

/-! The actual finite-model comparison carries its sheaf-resolution cup
to the balanced product on the original bounded crystalline groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech.IntrinsicComparison.frames p X Y f hp n
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n
local notation "KK" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic.underlyingComplex p X Y f hp n
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup.resolution p (ZMod p) w n
local notation "m" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n
local notation "cover" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve F
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechComplex.presheafComplex w n F

abbrev comparison (i : ℕ) :=
  Balanced.IntrinsicComparison.comparison p X Y f hp n I i

abbrev equivalence (i : ℕ) :=
  Balanced.IntrinsicComparison.equivalence p X Y f hp n I i

abbrev augmentationMap := Augmentation.IntrinsicIntrinsic.totalMap p X Y f hp n F

abbrev cup := Presheaf.CohomologyProduct.Cech.cohomologyCup N KK
  (SheafProduct.Intrinsic.sectionPairing p X Y f hp n)
  (SheafProduct.Intrinsic.sectionPairing_natural p X Y f hp n)
  (SheafProduct.Intrinsic.sectionPairing_differential p X Y f hp n)

theorem normalization (i : ℕ) (x : (A).homology i) :
    comparison p X Y f hp n i
      (HomologicalComplex.homologyMap (augmentationMap p X Y f hp n) i x) =
        BalancedBounded.PresheafCup.equivalence p (ZMod p) w n F cover i x := by
  have h := BalancedBounded.Augmentation.augmentation p (ZMod p) w n F cover K a m
    (GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.augmentation p X Y f hp n I) i x
  dsimp only [BalancedBounded.Augmentation.map] at h
  erw [Augmentation.IntrinsicIntrinsic.square] at h
  exact h

abbrev comparison_cup := MultiplicativeDescent.Comparison.multiplication
  (fun i => HomologicalComplex.homologyMap (augmentationMap p X Y f hp n) i)
  (fun i => comparison p X Y f hp n i)
  (fun i => (BalancedBounded.PresheafCup.equivalence p (ZMod p) w n F cover i).toEquiv)
  (Balanced.IntrinsicComparison.bijective p X Y f hp n I)
  (normalization p X Y f hp n)
  (fun i j x y => BalancedBounded.PresheafCup.cup p (ZMod p) w n F i j x y)
  (fun i j x y => cup p X Y f hp n i j x y)
  (fun i j x y => BalancedBounded.CechCup.cup p (ZMod p) w n F cover i j x y)
  (Augmentation.IntrinsicIntrinsic.totalMap_cup p X Y f hp n F)
  (BalancedBounded.PresheafCup.cup_comparison p (ZMod p) w n F cover)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BalancedProduct.Intrinsic
