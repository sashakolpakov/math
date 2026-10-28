import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorEquivalence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence
import Mathlib.Algebra.Homology.SingleHomology

/-! # Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Poincare.FreeDividedPoincare

noncomputable section

/-!
# The actual multivariable divided-power Poincaré homotopy

The polynomial-envelope coordinate basis identifies its PD de Rham
complex with its tensor coordinate complex. The proved PD algebra
equivalence transports this identification to the actual divided-power
algebra. Its integral coordinate contraction therefore gives a homotopy
equivalence of the actual PD de Rham complex with the coefficient ring.
The coefficient ring is arbitrary; no torsion-freeness hypothesis is used.
-/

open _root_.CategoryTheory

universe u

variable (R σ : Type u) [CommRing R] [Fintype σ]

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

attribute [local instance] Envelope.FreeDividedEnvelope.envelopeBaseAlgebra

local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.algebraEquiv R σ
local notation "he" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.algebraEquiv_isDPMorphism R σ
local notation "hi" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.algebraEquiv_symm_isDPMorphism R σ
local notation "base" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.base_le R σ
local notation "dE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I δ IP base
local notation "dG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.derivatives R σ

def envelopeDerivatives (i : σ) : Module.End R E := (dE i).toLinearMap

local notation "DE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Poincare.FreeDividedPoincare.envelopeDerivatives R σ

omit [Fintype σ] in
theorem envelopeDerivatives_commute (i j : σ) : Function.Commute (DE i) (DE j) :=
  Polynomial.EnvelopeForms.PolynomialEnvelopeForms.pderiv_commute R σ I δ IP base i j

local notation "commE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Poincare.FreeDividedPoincare.envelopeDerivatives_commute R σ
local notation "TE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ E DE commE
local notation "TG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.complex R σ

/-- The actual coefficient isomorphism intertwines every coordinate derivative. -/
def tensorIso : TE ≅ TG :=
  Koszul.TensorEquivalence.KoszulTensorEquivalence.complexIso R σ E G DE dG commE
    (KoszulHomotopy.FreeDividedKoszulHomotopy.commute R σ) (e).toLinearEquiv
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
  exact (tensorIso R σ).symm ≪≫
    (envelopeFormsIso R σ) ≪≫ dividedFormsIso R σ

/-- Integral Poincaré contraction on the actual multivariable PD form complex. -/
def homotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) (PD.DeRham.PDDeRham.complex R G IG γ) :=
  (KoszulHomotopy.FreeDividedKoszulHomotopy.homotopyEquiv R σ).trans
    (HomotopyEquiv.ofIso (complexIso R σ))

def augmentation : (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R) ⟶
    PD.DeRham.PDDeRham.complex R G IG γ := (homotopyEquiv R σ).hom

instance augmentation_quasiIso : QuasiIso (augmentation R σ) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv R σ)

def degreeZeroHomologyIso : (PD.DeRham.PDDeRham.complex R G IG γ).homology 0 ≅ ModuleCat.of R R :=
  ((homotopyEquiv R σ).toHomologyIso 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (ModuleCat.of R R)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Poincare.FreeDividedPoincare
