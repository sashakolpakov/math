import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CoordinateBasis
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Poincare

/-! # Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Forms.MultivariableForms

noncomputable section

/-! # Coordinate bases on actual multivariable divided-power forms -/

open _root_.CategoryTheory Classical

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a)) [Fintype σ]

local notation "P" => MvPolynomial σ R
local notation "IP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.polynomialIdeal R σ I
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ IP
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ IP
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ IP
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.dividedPowers R σ K h I δ hunit

attribute [local instance] Envelope.MultivariableEnvelope.envelopeBaseAlgebra

local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.algebraEquiv R σ K h I δ hunit
local notation "he" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.algebraEquiv_isDPMorphism R σ K h I δ hunit
local notation "hi" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.algebraEquiv_symm_isDPMorphism R σ K h I δ hunit
local notation "base" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.base_le R σ I
local notation "dE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP base
local notation "dG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation.derivation R σ K h I δ hunit
local notation "x" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1

def envelopeFormMap (n : ℕ) : PD.DeRham.PDDeRham.Form R E IE ε n →ₗ[R] PD.DeRham.PDDeRham.Form R G IG γ n :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (e).toAlgHom) he n

omit [Fintype σ] in
theorem envelopeFormMap_D (a : E) :
    envelopeFormMap R σ K h I δ hunit 1 (PD.OneForms.PDOneForms.D R E IE ε a) = PD.OneForms.PDOneForms.D R G IG γ (e a) :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_D (A := CommAlgCat.of R E) (B := CommAlgCat.of R G) e he hi a

/-- Expansion of the universal PD derivation in the actual divided coordinates. -/
theorem D_eq_sum (a : G) :
    PD.OneForms.PDOneForms.D R G IG γ a = ∑ i, dG i a • PD.OneForms.PDOneForms.D R G IG γ (x i) := by
  obtain ⟨a, rfl⟩ := (e).surjective a
  rw [← envelopeFormMap_D, Polynomial.EnvelopeForms.PolynomialEnvelopeForms.D_eq_sum R σ I δ IP base, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul (A := CommAlgCat.of R E) (B := CommAlgCat.of R G)
    (CommAlgCat.ofHom (e).toAlgHom) he 1 (dE i a)
    (PD.OneForms.PDOneForms.D R E IE ε (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP i))
  change envelopeFormMap R σ K h I δ hunit 1 (dE i a • _) =
    e (dE i a) • envelopeFormMap R σ K h I δ hunit 1 _ at hs
  have hc : e (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP i) = x i :=
    Envelope.MultivariableEnvelope.toDivided_coordinate R σ K h I δ hunit i
  rw [hs, envelopeFormMap_D, hc]
  exact congrArg (fun c : G => c • PD.OneForms.PDOneForms.D R G IG γ (x i))
    (PD.DerivationTransport.PDDerivationTransport.conjugate_apply_equiv R E G e (dE i) a).symm

omit [Fintype σ] in
theorem derivation_dpow_smul (i : σ) (n : ℕ) (a : G) (ha : a ∈ IG) :
    dG i ((γ).dpow (n + 1) a) = (γ).dpow n a • dG i a :=
  CoordinateDerivation.MultivariableCoordinateDerivation.derivation_dpow R σ K h I δ hunit i n ha

def basis : Module.Basis σ G (PD.DeRham.PDDeRham.Form R G IG γ 1) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis R G σ IG γ x dG (derivation_dpow_smul R σ K h I δ hunit)
    (D_eq_sum R σ K h I δ hunit)
    (fun i j => CoordinateDerivation.MultivariableCoordinateDerivation.derivation_coordinate R σ K h I δ hunit i j)

theorem basis_apply (i : σ) : basis R σ K h I δ hunit i = PD.OneForms.PDOneForms.D R G IG γ (x i) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis_apply R G σ IG γ x dG (derivation_dpow_smul R σ K h I δ hunit)
    (D_eq_sum R σ K h I δ hunit)
    (fun i j => CoordinateDerivation.MultivariableCoordinateDerivation.derivation_coordinate R σ K h I δ hunit i j) i

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Forms.MultivariableForms
