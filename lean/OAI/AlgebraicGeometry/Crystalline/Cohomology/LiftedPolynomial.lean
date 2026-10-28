import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison

/-! # Lifted Polynomial -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedPolynomial.LiftedPolynomialFrameFrobenius

noncomputable section

/-! # The explicit polynomial Frobenius with the original comparison coefficients -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B (MvPolynomial σ W) r hr hb
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k B Tower
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison.AffineCrystallineComparison.completedComplex p k B σ r hr hb
local notation "e" => WittVector.frobeniusEquiv p k
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.largeRestriction W e

def comparisonIso : ((LiftedCoefficientLarge.LiftedCoefficientTwist.lift W).mapHomologicalComplex (.up ℕ)).obj K ≅ C :=
  Iso.refl _

def smallMap : K ⟶ ((LiftedCoefficientLarge.LiftedCoefficientTwist.smallRestriction W e).mapHomologicalComplex (.up ℕ)).obj K :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.complexMap p k σ)

def complexMap : C ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj C :=
  (comparisonIso p k σ).inv ≫ LiftedCoefficientLarge.LiftedCoefficientTwist.map W e (smallMap p k σ) ≫
    ((Q).mapHomologicalComplex (.up ℕ)).map (comparisonIso p k σ).hom

theorem component (n : ℕ) (x : (K).X n) :
    ((complexMap p k σ).f n).hom (ULift.up (ULift.up x)) =
      ULift.up (ULift.up (WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.formMap p k σ n x)) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedPolynomial.LiftedPolynomialFrameFrobenius
