import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusSectionGenerators
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormSquare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistCoordinateForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusCoordinateForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusLiftedCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.RelativeCoordinateIdentification
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.AdditiveEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusLiftedAdditiveCoordinates

/-! # Frobenius Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusCoordinates.BigPolynomialFrobeniusRawCoordinates

noncomputable section

/-! # The original raw polynomial Frobenius maps satisfy the relative-form square -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B
  (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ bX
local notation "e" => WittVector.frobeniusEquiv p k
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e (DividedPowers.DPMorphism.isDPMorphism he) hb
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ring p k σ
local notation "G" => fun n => DividedPowerAlgebra (R n) (σ →₀ R n)

theorem coordinates (n j : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ (G n) j) :
    FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare.coordinates p k σ n j
      (FrobeniusSectionGenerators.BigPolynomialFrobeniusSectionGenerators.rawMap p k σ j n (ULift.up z)).down =
    FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.power p k σ n j
      (FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation.ambient p k σ n j
        (FrobeniusFormSquare.BigPolynomialFrobeniusFormSquare.coordinates p k σ n j z)) := by
  have hc := BigCrystalline.FrobeniusLiftedAdditiveCoordinates.BigCrystallineFrobeniusLiftedAdditiveCoordinates.coordinates p (Fact.out : p.Prime) W B σ
    (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism hb a j
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n) z
  have ha : RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification.coordinates p k σ n j
      (BigCrystalline.FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map p (Fact.out : p.Prime) W B σ
        (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B) I γ bX e (he).isDPMorphism hb a j
        (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n)
        (ULift.up z)).down =
      RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification.power p k σ n j
        (RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification.ambient p k σ n j
          (RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification.coordinates p k σ n j z)) := hc
  simpa only [RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification.coordinates_eq,
    RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification.power_eq, RelativeCoordinateIdentification.BigPolynomialRelativeCoordinateIdentification.ambient_eq,
    FrobeniusSectionGenerators.BigPolynomialFrobeniusSectionGenerators.rawMap] using ha

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusCoordinates.BigPolynomialFrobeniusRawCoordinates
