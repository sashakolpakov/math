import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationTransport

/-! # Derivation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation

noncomputable section

/-!
# Coordinate derivations on the actual multivariable divided-power algebra

The coordinate derivations of the polynomial envelope transfer through
the proved PD equivalence. Their action on divided coordinate powers
lowers the divided exponent over arbitrary coefficient rings, including
rings with torsion.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R]

local notation "I" => (⊥ : Ideal R)
local notation "δ" => dividedPowersBot R

local notation "P" => MvPolynomial σ R
local notation "IP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.polynomialIdeal R σ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ IP
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ IP
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ IP
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => RingHom.ker (AlgHom.toRingHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation R σ))
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers.FreeDividedPowers.dividedPowers R σ
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.algebraEquiv R σ

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ IP).comp (algebraMap R P)).toAlgebra

def derivation (i : σ) : Derivation R G G :=
  PD.DerivationTransport.PDDerivationTransport.conjugate R E G e
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeDividedEnvelope.base_le R σ) i)

theorem derivation_dpow (i : σ) (n : ℕ) {a : G} (ha : a ∈ IG) :
    derivation R σ i ((γ).dpow (n + 1) a) =
      (γ).dpow n a * derivation R σ i a :=
  PD.DerivationTransport.PDDerivationTransport.conjugate_dpow R E G e
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeDividedEnvelope.base_le R σ) i)
    IE IG ε γ (Envelope.FreeDividedEnvelope.algebraEquiv_symm_isDPMorphism R σ)
    (fun n _ ha => Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_dpow R σ I δ IP
      (Envelope.FreeDividedEnvelope.base_le R σ) i n ha) n ha

theorem derivation_coordinate (i j : σ) [Decidable (j = i)] :
    derivation R σ i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j) = if j = i then 1 else 0 := by
  have hc : e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP j) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j :=
    Envelope.FreeDividedEnvelope.toDivided_coordinate R σ j
  have hi : (e).symm (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j) = Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP j :=
    (congrArg (e).symm hc.symm).trans ((e).symm_apply_apply _)
  change e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeDividedEnvelope.base_le R σ) i
    ((e).symm (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j))) = _
  rw [hi, Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_coordinate]
  split_ifs <;> simp only [map_one, map_zero]

theorem derivation_generator_zero (i j : σ) :
    derivation R σ i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 0 j) = 0 := by
  change derivation R σ i (DividedPowerAlgebra.dp R 0 (Finsupp.single j (1 : R))) = 0
  rw [DividedPowerAlgebra.dp_zero, Derivation.map_one_eq_zero]

theorem derivation_generator_succ (i j : σ) (n : ℕ) [Decidable (j = i)] :
    derivation R σ i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n + 1) j) =
      if j = i then Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j else 0 := by
  rw [← Powers.FreeDividedPowers.coordinate_dpow R σ (n + 1) j,
    derivation_dpow R σ i n
      (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem R σ j),
    Powers.FreeDividedPowers.coordinate_dpow, derivation_coordinate]
  split_ifs <;> simp only [mul_one, mul_zero]

theorem derivations_commute (i j : σ) :
    Function.Commute (derivation R σ i) (derivation R σ j) := by
  intro a
  change e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeDividedEnvelope.base_le R σ) i
      ((e).symm (e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeDividedEnvelope.base_le R σ) j
        ((e).symm a))))) =
    e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeDividedEnvelope.base_le R σ) j
      ((e).symm (e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeDividedEnvelope.base_le R σ) i
        ((e).symm a)))))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  exact congrArg e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_commute R σ I δ IP
    (Envelope.FreeDividedEnvelope.base_le R σ) i j ((e).symm a))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation
