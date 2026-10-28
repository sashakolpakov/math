import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationTransport

/-! # Coordinate Derivation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation

noncomputable section

/-!
# Coordinate derivations on the actual multivariable divided-power algebra

The coordinate derivations of the polynomial envelope transfer through
the proved PD equivalence. Their action on divided coordinate powers
lowers the divided exponent without introducing denominators.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

local notation "P" => MvPolynomial σ R
local notation "IP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.polynomialIdeal R σ I
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ IP
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ IP
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ IP
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.dividedPowers R σ K h I δ hunit
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.algebraEquiv R σ K h I δ hunit

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ IP).comp (algebraMap R P)).toAlgebra

def derivation (i : σ) : Derivation R G G :=
  PD.DerivationTransport.PDDerivationTransport.conjugate R E G e
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.MultivariableEnvelope.base_le R σ I) i)

theorem derivation_dpow (i : σ) (n : ℕ) {a : G} (ha : a ∈ IG) :
    derivation R σ K h I δ hunit i ((γ).dpow (n + 1) a) =
      (γ).dpow n a * derivation R σ K h I δ hunit i a :=
  PD.DerivationTransport.PDDerivationTransport.conjugate_dpow R E G e
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.MultivariableEnvelope.base_le R σ I) i)
    IE IG ε γ (Envelope.MultivariableEnvelope.algebraEquiv_symm_isDPMorphism R σ K h I δ hunit)
    (fun n _ ha => Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_dpow R σ I δ IP
      (Envelope.MultivariableEnvelope.base_le R σ I) i n ha) n ha

theorem derivation_coordinate (i j : σ) [Decidable (j = i)] :
    derivation R σ K h I δ hunit i (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j) = if j = i then 1 else 0 := by
  have hc : e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP j) = DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j :=
    Envelope.MultivariableEnvelope.toDivided_coordinate R σ K h I δ hunit j
  have hi : (e).symm (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j) = Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP j :=
    (congrArg (e).symm hc.symm).trans ((e).symm_apply_apply _)
  change e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.MultivariableEnvelope.base_le R σ I) i
    ((e).symm (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j))) = _
  rw [hi, Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_coordinate]
  split_ifs <;> simp only [map_one, map_zero]

theorem derivation_generator_zero (i j : σ) :
    derivation R σ K h I δ hunit i (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 0 j) = 0 := by
  change derivation R σ K h I δ hunit i (DividedPowerAlgebra.dp R 0 (Finsupp.single j (1 : R))) = 0
  rw [DividedPowerAlgebra.dp_zero, Derivation.map_one_eq_zero]

theorem derivation_generator_succ (i j : σ) (n : ℕ) [Decidable (j = i)] :
    derivation R σ K h I δ hunit i (DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n + 1) j) =
      if j = i then DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j else 0 := by
  rw [← Multivariable.DividedPowers.MultivariableDividedPowers.coordinate_dpow R σ K h I δ hunit (n + 1) j,
    derivation_dpow R σ K h I δ hunit i n
      (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I j 1 one_ne_zero),
    Multivariable.DividedPowers.MultivariableDividedPowers.coordinate_dpow, derivation_coordinate]
  split_ifs <;> simp only [mul_one, mul_zero]

theorem derivations_commute (i j : σ) :
    Function.Commute (derivation R σ K h I δ hunit i) (derivation R σ K h I δ hunit j) := by
  intro a
  change e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.MultivariableEnvelope.base_le R σ I) i
      ((e).symm (e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.MultivariableEnvelope.base_le R σ I) j
        ((e).symm a))))) =
    e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.MultivariableEnvelope.base_le R σ I) j
      ((e).symm (e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.MultivariableEnvelope.base_le R σ I) i
        ((e).symm a)))))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  exact congrArg e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_commute R σ I δ IP
    (Envelope.MultivariableEnvelope.base_le R σ I) i j ((e).symm a))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation
