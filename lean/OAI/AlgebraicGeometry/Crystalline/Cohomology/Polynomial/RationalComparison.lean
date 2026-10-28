import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.IntegralComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtensionExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.RationalFrameFrobenius

/-! # Rational Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.RationalComparison.PolynomialRationalCrystallineComparison

noncomputable section

/-! # The polynomial rational comparison over the original Witt fraction field -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B (MvPolynomial σ W) r hr hb
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k B Tower
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor W K₀

def rationalEquiv (n : ℕ) :
    (WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.complex p k σ).homology n ≃ₗ[K₀]
      NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.rationalCohomology p k X n :=
  (Mapped.ComplexHomology.MappedComplexHomology.iso P C n).toLinearEquiv.trans
    ((IntegralComparison.PolynomialIntegralCrystallineComparison.integralEquiv p k σ n).baseChange W K₀ _ _)

omit [PerfectRing k p] in
theorem rationalEquiv_apply (n : ℕ)
    (x : (WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.complex p k σ).homology n) :
    rationalEquiv p k σ n x =
      (IntegralComparison.PolynomialIntegralCrystallineComparison.integralEquiv p k σ n).toLinearMap.baseChange K₀
        ((Mapped.ComplexHomology.MappedComplexHomology.iso P C n).hom x) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.RationalComparison.PolynomialRationalCrystallineComparison
