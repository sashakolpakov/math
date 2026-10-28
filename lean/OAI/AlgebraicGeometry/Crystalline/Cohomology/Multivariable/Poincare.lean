import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorEquivalence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence
import Mathlib.Algebra.Homology.SingleHomology

/-! # Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Poincare.MultivariablePoincare

noncomputable section

/-!
# The actual multivariable divided-power Poincaré homotopy

The polynomial-envelope coordinate basis identifies its PD de Rham
complex with its tensor coordinate complex. The proved PD algebra
equivalence transports this identification to the actual divided-power
algebra. Its integral coordinate contraction therefore gives a homotopy
equivalence of the actual PD de Rham complex with the coefficient ring.
-/

open _root_.CategoryTheory

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
local notation "dG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.derivatives R σ K h I δ hunit

def envelopeDerivatives (i : σ) : Module.End R E := (dE i).toLinearMap

local notation "DE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Poincare.MultivariablePoincare.envelopeDerivatives R σ I δ

omit [Fintype σ] in
theorem envelopeDerivatives_commute (i j : σ) : Function.Commute (DE i) (DE j) :=
  Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_commute R σ I δ IP base i j

local notation "commE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Poincare.MultivariablePoincare.envelopeDerivatives_commute R σ I δ
local notation "TE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ E DE commE
local notation "TG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.complex R σ K h I δ hunit

/-- The actual coefficient isomorphism intertwines every coordinate derivative. -/
def tensorIso : TE ≅ TG :=
  Koszul.TensorEquivalence.KoszulTensorEquivalence.complexIso R σ E G DE dG commE
    (KoszulHomotopy.MultivariableKoszulHomotopy.commute R σ K h I δ hunit) (e).toLinearEquiv
    (fun i a => (PD.DerivationTransport.PDDerivationTransport.conjugate_apply_equiv R E G e (dE i) a).symm)

def dividedFormsIso : PD.DeRham.PDDeRham.complex R E IE ε ≅ PD.DeRham.PDDeRham.complex R G IG γ :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.complexIso (A := CommAlgCat.of R E) (B := CommAlgCat.of R G) e he hi

def envelopeFormsIso [LinearOrder σ] : TE ≅ PD.DeRham.PDDeRham.complex R E IE ε :=
  PD.DeRhamTensor.PDDeRhamTensor.complexIso R E σ IE ε (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP) DE
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.D_eq_sum R σ I δ IP base)
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis R σ I δ IP base)
    (Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis_apply R σ I δ IP base) commE

/-- The tensor coordinate complex is the actual PD de Rham complex. -/
def complexIso : TG ≅ PD.DeRham.PDDeRham.complex R G IG γ := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact (tensorIso R σ K h I δ hunit).symm ≪≫
    (envelopeFormsIso R σ I δ) ≪≫ dividedFormsIso R σ K h I δ hunit

/-- Integral Poincaré contraction on the actual multivariable PD form complex. -/
def homotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) (PD.DeRham.PDDeRham.complex R G IG γ) :=
  (KoszulHomotopy.MultivariableKoszulHomotopy.homotopyEquiv R σ K h I δ hunit).trans
    (HomotopyEquiv.ofIso (complexIso R σ K h I δ hunit))

def augmentation : (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R) ⟶
    PD.DeRham.PDDeRham.complex R G IG γ := (homotopyEquiv R σ K h I δ hunit).hom

instance augmentation_quasiIso : QuasiIso (augmentation R σ K h I δ hunit) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv R σ K h I δ hunit)

def degreeZeroHomologyIso : (PD.DeRham.PDDeRham.complex R G IG γ).homology 0 ≅ ModuleCat.of R R :=
  ((homotopyEquiv R σ K h I δ hunit).toHomologyIso 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (ModuleCat.of R R)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Poincare.MultivariablePoincare
