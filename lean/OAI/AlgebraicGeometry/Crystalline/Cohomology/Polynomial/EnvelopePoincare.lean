import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Poincare

/-! # Envelope Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopePoincare.PolynomialEnvelopePoincare

noncomputable section

/-!
# Poincaré lemma for the actual polynomial PD envelope

The proved PD algebra isomorphism transfers the integral and completed
augmented sequences to the universal relative envelope. No exactness
property of completion is assumed.
-/

open _root_.CategoryTheory

universe u

variable (R K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R (Polynomial R) I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.polynomialIdeal R I)
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R (Polynomial R) I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.polynomialIdeal R I)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R (Polynomial R) I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.polynomialIdeal R I)
local notation "G" => DividedPowerAlgebra R R
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal R I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers R K h I δ hunit

attribute [local instance] Envelope.PolynomialEnvelope.envelopeBaseAlgebra

local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.algebraEquiv R K h I δ hunit
local notation "he" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.algebraEquiv_isDPMorphism R K h I δ hunit
local notation "hi" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.algebraEquiv_symm_isDPMorphism R K h I δ hunit
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R E IE ε
local notation "DG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R G IG γ

def formsEquiv (n : ℕ) : PD.DeRham.PDDeRham.Form R E IE ε n ≃ₗ[R] PD.DeRham.PDDeRham.Form R G IG γ n :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv (A := CommAlgCat.of R E) (B := CommAlgCat.of R G) e he hi n

theorem formsEquiv_D (a : E) : formsEquiv R K h I δ hunit 1 (D a) = DG (e a) :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_D (A := CommAlgCat.of R E) (B := CommAlgCat.of R G) e he hi a

theorem differential_constants : (D).toLinearMap.comp (Algebra.linearMap R E) = 0 := by
  apply LinearMap.ext
  intro a
  exact (D).map_algebraMap a

def sequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (Algebra.linearMap R E) (D).toLinearMap
    (differential_constants R I δ)

def sequenceIso : sequence R I δ ≅ Divided.PolynomialPoincare.DividedPolynomialPoincare.sequence R K h I δ hunit :=
  ShortComplex.isoMk (Iso.refl _) (LinearEquiv.toModuleIso (e).toLinearEquiv)
    (LinearEquiv.toModuleIso (formsEquiv R K h I δ hunit 1))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact ((e).commutes a).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (formsEquiv_D R K h I δ hunit a).symm)

include h hunit in
/-- The augmented de Rham sequence of the actual polynomial PD envelope is exact. -/
theorem sequence_shortExact : (sequence R I δ).ShortExact :=
  ShortComplex.shortExact_of_iso (sequenceIso R K h I δ hunit).symm
    (Divided.PolynomialPoincare.DividedPolynomialPoincare.sequence_shortExact R K h I δ hunit)

include h hunit in
theorem higher_form_eq_zero (n : ℕ) (hn : 2 ≤ n) (ω : PD.DeRham.PDDeRham.Form R E IE ε n) : ω = 0 := by
  apply (formsEquiv R K h I δ hunit n).injective
  rw [map_zero]
  exact Divided.PolynomialPoincare.DividedPolynomialPoincare.higher_form_eq_zero R K h I δ hunit n hn _

variable (L : Ideal R)

def completedSequence : ShortComplex (ModuleCat.{u} (AdicCompletion L R)) :=
  ShortComplex.moduleCatMk (AdicCompletion.map L (Algebra.linearMap R E))
    (AdicCompletion.map L (D).toLinearMap) (by
      apply LinearMap.ext
      intro a
      rw [LinearMap.comp_apply, AdicCompletion.map_comp_apply,
        differential_constants, AdicCompletion.map_zero, LinearMap.zero_apply])

theorem constants_commute :
    (e).toLinearMap.comp (Algebra.linearMap R E) = Algebra.linearMap R G := by
  apply LinearMap.ext
  exact (e).commutes

theorem differential_commute :
    (formsEquiv R K h I δ hunit 1).toLinearMap.comp (D).toLinearMap =
      (DG).toLinearMap.comp (e).toLinearMap := by
  apply LinearMap.ext
  exact formsEquiv_D R K h I δ hunit

def completedSequenceIso : completedSequence R I δ L ≅
    Poincare.PolynomialPoincare.sequence R K h I δ hunit L :=
  ShortComplex.isoMk (Iso.refl _)
    (LinearEquiv.toModuleIso (AdicCompletion.congr L (e).toLinearEquiv))
    (LinearEquiv.toModuleIso (AdicCompletion.congr L (formsEquiv R K h I δ hunit 1)))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change AdicCompletion L R at a
      change AdicCompletion.map L (Algebra.linearMap R G) a =
        AdicCompletion.map L (e).toLinearMap (AdicCompletion.map L (Algebra.linearMap R E) a)
      rw [AdicCompletion.map_comp_apply, constants_commute])
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change AdicCompletion L E at a
      change AdicCompletion.map L (DG).toLinearMap (AdicCompletion.map L (e).toLinearMap a) =
        AdicCompletion.map L (formsEquiv R K h I δ hunit 1).toLinearMap
          (AdicCompletion.map L (D).toLinearMap a)
      rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply, differential_commute])

include h hunit in
/-- Completion of the envelope's actual augmented de Rham sequence is exact. -/
theorem completedSequence_shortExact : (completedSequence R I δ L).ShortExact :=
  ShortComplex.shortExact_of_iso (completedSequenceIso R K h I δ hunit L).symm
    (Poincare.PolynomialPoincare.sequence_shortExact R K h I δ hunit L)

include h hunit in
theorem completed_higher_form_eq_zero (n : ℕ) (hn : 2 ≤ n)
    (ω : AdicCompletion L (PD.DeRham.PDDeRham.Form R E IE ε n)) : ω = 0 := by
  apply (AdicCompletion.congr L (formsEquiv R K h I δ hunit n)).injective
  rw [map_zero]
  exact Poincare.PolynomialPoincare.higher_form_eq_zero R K h I δ hunit L n hn _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopePoincare.PolynomialEnvelopePoincare
