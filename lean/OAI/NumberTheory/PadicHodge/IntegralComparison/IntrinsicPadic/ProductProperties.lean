import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReductionProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameBijective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupCoverIndependence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SmoothProperWittCup

/-! # Product Properties -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ProductProperties.IntrinsicComparison

noncomputable section

/-! The literal finite ordinary comparison is bijective and preserves the
balanced cup used by the original integral crystalline inverse limit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem restriction_bijective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (K : CochainComplex (ModuleCat S) ℕ) (i : ℕ) :
    Function.Bijective (RestrictScalarsCochainCup.map R S K i) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (ModuleCat.restrictScalars (algebraMap R S)) K i).symm.toLinearEquiv.bijective

section General

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [hYsep : IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)

local instance coefficients : Algebra W ℤ_[p] := GeometricComparison.WittAlgebra.PadicWittAlgebra.coefficientAlgebra p
local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem wittMap_bijective (i : ℕ) :
    Function.Bijective (SmallProductMap.Intrinsic.wittMap p X n i) :=
  (HomologicalComplex.homologyMapIso (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).symm i).toLinearEquiv.bijective.comp
    (restriction_bijective (R := W) (S := ℤ_[p]) (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n) i)

omit [IsSeparated Y.hom] in
theorem frameMap_bijective (i : ℕ) :
    Function.Bijective (SmallProductMap.Intrinsic.frameMap p X Y f hp n i) := by
  let : QuasiIso (ReducedTotalProduct.Intrinsic.totalMap p X Y f hp n) :=
    ReducedTotalProduct.Intrinsic.quasiIso p X Y f hp n
  exact (isoOfQuasiIsoAt (ReducedTotalProduct.Intrinsic.totalMap p X Y f hp n) i).toLinearEquiv.bijective.comp
    (wittMap_bijective p X n i)

theorem rawFrameMap_bijective (i : ℕ) :
    Function.Bijective (FrameProduct.IntrinsicRaw.map p X Y f hp n i) :=
  (FrameBijective.IntrinsicComparison.comparison_bijective p X Y f hp n i).comp
    (Crystalline.CoefficientCohomologyCup.map_bijective W
      (FrameProductMap.Intrinsic.complex p X Y f hp n) i)

theorem smallMap_bijective (i : ℕ) :
    Function.Bijective (SmallProductMap.Intrinsic.map p X Y f hp n i) :=
  (rawFrameMap_bijective p X Y f hp n i).comp (frameMap_bijective p X Y f hp n i)

theorem comparison_bijective (i : ℕ) :
    Function.Bijective (ReductionProduct.Intrinsic.comparison p X Y f hp n i) :=
  (smallMap_bijective p X Y f hp n i).comp
    (HomologicalComplex.homologyMapIso (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).symm i).toLinearEquiv.bijective

theorem reductionComparison_eq_zero (i : ℕ) (x : (K).homology i)
    (hx : ∀ n : ℕ, ReductionProduct.Intrinsic.reductionComparison p X Y f hp n i x = 0) :
    x = 0 := by
  apply OrdinaryReduction.IntrinsicOrdinary.eq_zero p X i x
  intro n
  apply (comparison_bijective p X Y f hp n i).injective
  exact (hx n).trans (map_zero (ReductionProduct.Intrinsic.comparison p X Y f hp n i)).symm

end General

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)

attribute [local instance] coefficients separated

omit [X.left.IsSeparated] in
theorem cup_eq (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n j) :
    BalancedBounded.CechCup.cup p (ZMod p) w n
      (BoundedCech.IntrinsicComparison.frames p X Y f hp n)
      (GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n) i j x y =
    Balanced.SmoothProperWittCup.cup p (ZMod p) Y n i j x y :=
  Balanced.CupCoverIndependence.cup_eq p (ZMod p) w n
    (BoundedCech.IntrinsicComparison.frames p X Y f hp n)
    (SmoothProper.WittFrameFamily.Family.frame p (ZMod p) Y n)
    (GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n)
    (SmoothProper.WittFrameCover.covering p (ZMod p) Y n) i j x y

attribute [local irreducible] Cochain.CohomologyCup.cohomologyCup

include p X Y f hp n in
abbrev reductionComparison_cup (i j : ℕ) (x : (K).homology i) (y : (K).homology j) :=
  (ReductionProduct.Intrinsic.reductionComparison_cup p X Y f hp n i j x y).trans
    (cup_eq p X Y f hp n i j _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ProductProperties.IntrinsicComparison
