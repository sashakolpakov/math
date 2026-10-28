import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.IntegralComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.HomologyFrobenius

/-! # Integral Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.IntegralFrobenius.PolynomialIntegralFrobenius

noncomputable section

/-! # The polynomial integral comparison intertwines the original crystalline Frobenius -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B (MvPolynomial σ W) r hr hb
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k B Tower
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hb
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "e" => WittVector.frobeniusEquiv p k
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.largeRestriction W e
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.complexMap p k σ

omit [PerfectRing k p] in
theorem comparison_apply (n : ℕ) (x : (C).homology n) :
    IntegralComparison.PolynomialIntegralCrystallineComparison.integralEquiv p k σ n x =
      NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n
        ((Big.AffineComparison.BigAffineCrystallineComparison.homologyIso p k B σ r hr hb n).hom
          (HomologyFrobenius.PolynomialHomologyFrobenius.lift p k σ n x)) := rfl

theorem intertwines (n : ℕ) (x : (C).homology n) :
    IntegralComparison.PolynomialIntegralCrystallineComparison.integralEquiv p k σ n
      (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap F n x) =
      NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.integralFrobenius p k X n
        (IntegralComparison.PolynomialIntegralCrystallineComparison.integralEquiv p k σ n x) := by
  let c := Big.AffineComparison.BigAffineCrystallineComparison.homologyIso p k B σ r hr hb n
  let a := NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n
  let y := HomologyFrobenius.PolynomialHomologyFrobenius.lift p k σ n x
  have hs := HomologyFrobenius.PolynomialHomologyFrobenius.intertwines p k σ n x
  have hc := Big.AffineFrobenius.BigAffineCrystallineFrobenius.original p k B σ r hr hb n y
  have hi := NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.integral_intertwines p k X n (c.hom y)
  rw [comparison_apply, comparison_apply]
  exact (congrArg (fun z => a (c.hom z)) hs).trans ((congrArg a hc).trans hi.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.IntegralFrobenius.PolynomialIntegralFrobenius
