import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusIdentification
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientOn
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientTwistHomologyInverse

/-! # Homology Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.HomologyFrobenius.PolynomialHomologyFrobenius

noncomputable section

/-! # The original completed crystalline Frobenius on small polynomial homology -/

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
local notation "e" => WittVector.frobeniusEquiv p k
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.lift W
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge.LiftedCoefficientTwist.largeRestriction W e
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.coefficients p k
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.complexMap p k σ

def comparisonIso (n : ℕ) : (P).obj ((C).homology n) ≅ (D).homology n :=
  (Mapped.ComplexHomology.MappedComplexHomology.iso P C n).symm

def lift (n : ℕ) (x : (C).homology n) : (D).homology n :=
  Module.AdditiveEvaluation.ModuleAdditiveEvaluation.map (comparisonIso p k σ n).hom (ULift.up (ULift.up x))

def smallAction (n : ℕ) (x : (C).homology n) : (C).homology n :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap F n x

def action (n : ℕ) : (D).homology n →+ (D).homology n :=
  RestrictedHomology.RestrictedHomologyAction.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).toRingHom D
    (Big.AffineFrobenius.BigAffineCrystallineFrobenius.complexMap p k B σ r hr hb) n

omit [Fintype σ] [LinearOrder σ] in
theorem liftedMap_eq : LiftedPolynomial.LiftedPolynomialFrameFrobenius.complexMap p k σ =
    LiftedCoefficientLarge.LiftedCoefficientTwist.map W e (LiftedPolynomial.LiftedPolynomialFrameFrobenius.smallMap p k σ) := by
  let L := ((P).mapHomologicalComplex (.up ℕ)).obj C
  let G := (T).mapHomologicalComplex (.up ℕ)
  let f := LiftedCoefficientLarge.LiftedCoefficientTwist.map W e (LiftedPolynomial.LiftedPolynomialFrameFrobenius.smallMap p k σ)
  exact (Category.id_comp (f ≫ G.map (𝟙 L))).trans
    ((congrArg (fun g => f ≫ g) (G.map_id L)).trans (Category.comp_id f))

theorem intertwines (n : ℕ) (x : (C).homology n) :
    lift p k σ n (smallAction p k σ n x) = action p k σ n (lift p k σ n x) := by
  have hm := (BigPolynomial.FrobeniusIdentification.BigPolynomialFrobeniusIdentification.original p k σ).trans (liftedMap_eq p k σ)
  have hh := congrArg (fun f =>
    RestrictedHomology.RestrictedHomologyAction.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).toRingHom D f n
      (lift p k σ n x)) hm
  have hl := CoefficientTwistHomologyInverse.LiftedCoefficientTwistHomologyInverse.semilinear W e C F n x
  exact hl.trans hh.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.HomologyFrobenius.PolynomialHomologyFrobenius
