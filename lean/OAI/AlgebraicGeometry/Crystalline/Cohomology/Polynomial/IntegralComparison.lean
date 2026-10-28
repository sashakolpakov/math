import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientOf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedPolynomial
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Integral Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.IntegralComparison.PolynomialIntegralCrystallineComparison

noncomputable section

/-! # The original integral crystalline cohomology of polynomial affine space -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B (MvPolynomial σ W) r hr hb
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k B Tower
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.lift W

def liftedHomologyIso (n : ℕ) :
    (P).obj ((C).homology n) ≅
      ModuleCat.of R (NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X n) :=
  (Mapped.ComplexHomology.MappedComplexHomology.iso P C n).symm ≪≫
    Big.AffineComparison.BigAffineCrystallineComparison.homologyIso p k B σ r hr hb n ≪≫
    (NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison.integralEquiv p k X n).toModuleIso

def integralEquiv (n : ℕ) :
    (C).homology n ≃ₗ[W] NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X n :=
  LiftedCoefficientOf.LiftedCoefficientEquivalence.ofIso W (liftedHomologyIso p k σ n)

theorem integralEquiv_apply (n : ℕ) (x : (C).homology n) :
    integralEquiv p k σ n x =
      (liftedHomologyIso p k σ n).hom (ULift.up (ULift.up x)) :=
  LiftedCoefficientOf.LiftedCoefficientEquivalence.ofIso_apply W (liftedHomologyIso p k σ n) x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.IntegralComparison.PolynomialIntegralCrystallineComparison
