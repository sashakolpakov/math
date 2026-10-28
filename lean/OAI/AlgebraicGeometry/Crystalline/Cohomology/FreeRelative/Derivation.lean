import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation

/-! # Derivation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Derivation.FreeRelativeDerivation

noncomputable section

/-!
# Coordinate derivations on the actual multivariable divided-power algebra

The coordinate derivations of the polynomial envelope transfer through
the proved PD equivalence. Their action on divided coordinate powers
lowers the divided exponent without introducing denominators.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

local notation "P" => MvPolynomial σ R
local notation "IP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.polynomialIdeal R σ I
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ IP
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ IP
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ IP
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.algebraEquiv R σ I δ

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ IP).comp (algebraMap R P)).toAlgebra

def derivation (i : σ) : Derivation R G G :=
  PD.DerivationTransport.PDDerivationTransport.conjugate R E G e
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I) i)

theorem derivation_dpow (i : σ) (n : ℕ) {a : G} (ha : a ∈ IG) :
    derivation R σ I δ i ((γ).dpow (n + 1) a) =
      (γ).dpow n a * derivation R σ I δ i a :=
  PD.DerivationTransport.PDDerivationTransport.conjugate_dpow R E G e
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I) i)
    IE IG ε γ (Envelope.FreeRelativeEnvelope.algebraEquiv_symm_isDPMorphism R σ I δ)
    (fun n _ ha => Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_dpow R σ I δ IP
      (Envelope.FreeRelativeEnvelope.base_le R σ I) i n ha) n ha

theorem derivation_coordinate (i j : σ) [Decidable (j = i)] :
    derivation R σ I δ i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j) = if j = i then 1 else 0 := by
  have hc : e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP j) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j :=
    Envelope.FreeRelativeEnvelope.toDivided_coordinate R σ I δ j
  have hi : (e).symm (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j) = Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP j :=
    (congrArg (e).symm hc.symm).trans ((e).symm_apply_apply _)
  change e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I) i
    ((e).symm (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 j))) = _
  rw [hi, Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_coordinate]
  split_ifs <;> simp only [map_one, map_zero]

theorem derivation_generator_zero (i j : σ) :
    derivation R σ I δ i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 0 j) = 0 := by
  change derivation R σ I δ i (DividedPowerAlgebra.dp R 0 (Finsupp.single j (1 : R))) = 0
  rw [DividedPowerAlgebra.dp_zero, Derivation.map_one_eq_zero]

theorem derivation_generator_succ (i j : σ) (n : ℕ) [Decidable (j = i)] :
    derivation R σ I δ i (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n + 1) j) =
      if j = i then Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n j else 0 := by
  rw [← Powers.FreeRelativePowers.coordinate_dpow R σ I δ (n + 1) j,
    derivation_dpow R σ I δ i n
      (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I j 1 one_ne_zero),
    Powers.FreeRelativePowers.coordinate_dpow, derivation_coordinate]
  split_ifs <;> simp only [mul_one, mul_zero]

theorem derivations_commute (i j : σ) :
    Function.Commute (derivation R σ I δ i) (derivation R σ I δ j) := by
  intro a
  change e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I) i
      ((e).symm (e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I) j
        ((e).symm a))))) =
    e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I) j
      ((e).symm (e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP (Envelope.FreeRelativeEnvelope.base_le R σ I) i
        ((e).symm a)))))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  exact congrArg e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_commute R σ I δ IP
    (Envelope.FreeRelativeEnvelope.base_le R σ I) i j ((e).symm a))

theorem derivation_ext (D₁ D₂ : Derivation R G G)
    (hg : ∀ (n : ℕ) (i : σ), D₁ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = D₂ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i)) : D₁ = D₂ := by
  classical
  have hm (d : σ →₀ ℕ) : D₁ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = D₂ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) := by
    have hp (s : Finset σ) : D₁ (∏ i ∈ s, Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (d i) i) =
        D₂ (∏ i ∈ s, Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (d i) i) := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.prod_empty, Derivation.map_one_eq_zero]
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, D₁.leibniz, D₂.leibniz, ih, hg]
    exact hp d.support
  have hl : D₁.toLinearMap = D₂.toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    exact hm d
  exact Derivation.ext (LinearMap.congr_fun hl)

/-- Relative base divided powers do not change the actual coordinate derivative. -/
theorem derivation_eq_free (i : σ) :
    derivation R σ I δ i = FreeDivided.Derivation.FreeDividedDerivation.derivation R σ i := by
  classical
  apply derivation_ext R σ
  intro n j
  cases n with
  | zero => rw [derivation_generator_zero, FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_zero]
  | succ n => rw [derivation_generator_succ, FreeDivided.Derivation.FreeDividedDerivation.derivation_generator_succ]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Derivation.FreeRelativeDerivation
