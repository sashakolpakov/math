import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusReduction
import OAI.NumberTheory.PadicHodge.GeometricComparison.LinearEquivZero
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.OperatorDivisibility

/-! # Integral Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFrobenius.IntrinsicPadicIntegralFrobenius

noncomputable section

/-! Transported integral crystalline Frobenius is prime-divisible on
the actual first integral Hodge step of a smooth proper p-adic model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p

local notation "e" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective
local notation "g" => OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y
local notation "φ" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral p g
local notation "r" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.restriction p Y 0
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback.pullback p Y g 0

def map : Module.End ℤ_[p] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :=
  (e).symm.toLinearMap.comp ((φ).comp (e).toLinearMap)

def reduction : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 →ₗ[ℤ_[p]]
    CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.bounded p Y 0 :=
  (r).comp ((e).toLinearMap.comp (IntrinsicPadicIntegralFrobenius.map p X Y f hp I hprojective))

theorem reduction_eq : reduction p X Y f hp I hprojective =
    (b).comp ((CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.finiteEquiv p X Y f hp I 0).toLinearMap.comp
      (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X 1)) :=
  LinearEquivZero.LinearEquivReductionZero.linearMap e r φ b
    (CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.finiteEquiv p X Y f hp I 0).toLinearMap
    (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X 1)
    (CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.square p X Y f hp I hprojective 0)
    (CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback.natural p Y g 0)

theorem reduction_zero (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1)
    (hx : x ∈ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[p] X 1 1) :
    reduction p X Y f hp I hprojective x = 0 :=
  (LinearMap.congr_fun (reduction_eq p X Y f hp I hprojective) x).trans
    (FrobeniusReduction.IntrinsicPadicFrobeniusHodgeReduction.zero p X Y f hp I x hx)

theorem divisible (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1)
    (hx : x ∈ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[p] X 1 1) :
    ∃ y, IntrinsicPadicIntegralFrobenius.map p X Y f hp I hprojective x = (p : ℤ_[p]) • y :=
  Integral.OperatorDivisibility.IntegralOperatorDivisibility.divisible (e).toLinearMap r (IntrinsicPadicIntegralFrobenius.map p X Y f hp I hprojective) (p : ℤ_[p])
    (CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.zero_iff_prime_multiple p X Y f hp I hprojective) x
    (reduction_zero p X Y f hp I hprojective x hx)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFrobenius.IntrinsicPadicIntegralFrobenius
