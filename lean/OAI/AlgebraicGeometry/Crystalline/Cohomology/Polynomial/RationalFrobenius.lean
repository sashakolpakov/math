import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.RationalComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.IntegralFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.BaseChangeHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.BaseChangeNaturality

/-! # Rational Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.RationalFrobenius.PolynomialRationalCrystallineFrobenius

noncomputable section

/-! # Bijectivity of the original rational crystalline Frobenius for polynomial affine space -/

open _root_.CategoryTheory
open scoped TensorProduct

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
local notation "e" => WittVector.frobeniusEquiv p k
local notation "t" => OAI.AlgebraicGeometry.Crystalline.Cohomology.RationalPolynomial.RationalPolynomialCoefficientFrobenius.scalarEquiv p k
local notation "ht" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.scalar_base p k
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.complexMap p k σ

omit [Fintype σ] [LinearOrder σ] in
theorem genericMap_eq : Semilinear.BaseChangeHomology.SemilinearBaseChangeHomology.map W K₀ e t ht C F =
    WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.complexMap p k σ := rfl

omit [Fintype σ] [LinearOrder σ] in
theorem homology_conjugation (n : ℕ) (z : K₀ ⊗[W] (C).homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso P C n).hom
      (WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.frobenius p k σ n
        ((Mapped.ComplexHomology.MappedComplexHomology.iso P C n).inv z)) =
      NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange (e).toRingHom (t).toRingHom ht
        (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap F n) z := by
  simpa only [genericMap_eq, WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.frobenius] using
    Semilinear.BaseChangeHomology.SemilinearBaseChangeHomology.conjugation W K₀ e t ht C F n z

theorem intertwines (n : ℕ)
    (x : (WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.complex p k σ).homology n) :
    RationalComparison.PolynomialRationalCrystallineComparison.rationalEquiv p k σ n
      (WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.frobenius p k σ n x) =
      NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.rationalFrobenius p k X n
        (RationalComparison.PolynomialRationalCrystallineComparison.rationalEquiv p k σ n x) := by
  let c := Mapped.ComplexHomology.MappedComplexHomology.iso P C n
  let a := IntegralComparison.PolynomialIntegralCrystallineComparison.integralEquiv p k σ n
  let f := WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.frobenius p k σ n
  have hc := homology_conjugation p k σ n (c.hom x)
  have hi := (congrArg (fun y => c.hom (f y)) (ModuleCat.inv_hom_apply c x)).symm.trans hc
  have hn := Semilinear.BaseChangeNaturality.SemilinearBaseChangeNaturality.naturality (e).toRingHom (t).toRingHom ht
    (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap F n) (NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.integralFrobenius p k X n)
    a.toLinearMap (IntegralFrobenius.PolynomialIntegralFrobenius.intertwines p k σ n) (c.hom x)
  exact (congrArg (a.toLinearMap.baseChange K₀) hi).trans hn

theorem bijective (n : ℕ) :
    Function.Bijective (NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.rationalFrobenius p k X n) := by
  let c := RationalComparison.PolynomialRationalCrystallineComparison.rationalEquiv p k σ n
  let f := WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.frobenius p k σ n
  let g := NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius.rationalFrobenius p k X n
  have heq : g ∘ c = c ∘ f := funext (fun x => (intertwines p k σ n x).symm)
  have hcomp : Function.Bijective (g ∘ c) :=
    heq.symm ▸ c.bijective.comp (WittPolynomial.RationalFrameFrobenius.WittPolynomialRationalFrameFrobenius.frobenius_bijective p k σ n)
  exact (Function.Bijective.of_comp_iff g c.bijective).mp hcomp

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.RationalFrobenius.PolynomialRationalCrystallineFrobenius
