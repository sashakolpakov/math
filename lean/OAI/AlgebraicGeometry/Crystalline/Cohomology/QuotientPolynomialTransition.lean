import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialMk

/-! # Quotient Polynomial Transition -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialTransition.QuotientPolynomialTransitions

noncomputable section

/-!
# Compatibility of the finite-level local Poincaré contractions

Reduction between base ideals commutes with the actual divided powers,
derivative, primitive, and primitive on one-forms. These are the identities
needed to pass the split exact sequences to an inverse limit.
-/

universe u

variable (R K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))
  (L M : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ L)
  (hM : DividedPowers.IsSubDPIdeal δ M) (hML : M ≤ L)

local notation "G" => DividedPowerAlgebra R R
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal R I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers R K h I δ hunit
local notation "BL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.Ring R L
local notation "BM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.Ring R M
local notation "IL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.ideal R I L
local notation "IM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.ideal R I M
local notation "δL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.dividedPowers R K h I δ hunit L hL
local notation "δM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.dividedPowers R K h I δ hunit M hM
local notation "qL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.quotient R L
local notation "qM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.quotient R M

def transition : BM →ₐ[R] BL := Ideal.Quotient.factorₐ R (Ideal.map_mono hML)

@[simp] theorem transition_quotient (a : G) : transition R L M hML (qM a) = qL a := rfl

theorem transition_isDPMorphism :
    DividedPowers.IsDPMorphism δM δL (transition R L M hML).toRingHom := by
  apply DividedPowers.IsDPMorphism.of_comp γ δM δL (qM).toRingHom
    (transition R L M hML).toRingHom rfl
    (QuotientPolynomialEq.QuotientPolynomialForms.quotient_isDPMorphism R K h I δ hunit M hM)
  exact QuotientPolynomialEq.QuotientPolynomialForms.quotient_isDPMorphism R K h I δ hunit L hL

theorem derivation_transition (a : BM) :
    QuotientPolynomialEq.QuotientPolynomialForms.derivation R K h L (transition R L M hML a) =
      transition R L M hML (QuotientPolynomialEq.QuotientPolynomialForms.derivation R K h M a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change QuotientPolynomialEq.QuotientPolynomialForms.derivation R K h L (transition R L M hML (qM a)) =
    transition R L M hML (QuotientPolynomialEq.QuotientPolynomialForms.derivation R K h M (qM a))
  rw [transition_quotient, QuotientPolynomialEq.QuotientPolynomialForms.derivation_quotient,
    QuotientPolynomialEq.QuotientPolynomialForms.derivation_quotient, transition_quotient]

theorem primitive_transition (a : BM) :
    QuotientPolynomialMk.QuotientPolynomialPoincare.primitive R K h L (transition R L M hML a) =
      transition R L M hML (QuotientPolynomialMk.QuotientPolynomialPoincare.primitive R K h M a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change QuotientPolynomialMk.QuotientPolynomialPoincare.primitive R K h L (transition R L M hML (qM a)) =
    transition R L M hML (QuotientPolynomialMk.QuotientPolynomialPoincare.primitive R K h M (qM a))
  rw [transition_quotient, QuotientPolynomialMk.QuotientPolynomialPoincare.primitive_quotient,
    QuotientPolynomialMk.QuotientPolynomialPoincare.primitive_quotient, transition_quotient]

def formMap (n : ℕ) : PD.DeRham.PDDeRham.Form R BM IM δM n →ₗ[R] PD.DeRham.PDDeRham.Form R BL IL δL n :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (transition R L M hML))
    (transition_isDPMorphism R K h I δ hunit L M hL hM hML) n

theorem formMap_D (a : BM) :
    formMap R K h I δ hunit L M hL hM hML 1 (PD.OneForms.PDOneForms.D R BM IM δM a) =
      PD.OneForms.PDOneForms.D R BL IL δL (transition R L M hML a) :=
  PD.FormSurjective.PDFormSurjective.formMap_D (CommAlgCat.ofHom (transition R L M hML))
    (transition_isDPMorphism R K h I δ hunit L M hL hM hML) a

theorem toRing_formMap (ω : PD.DeRham.PDDeRham.Form R BM IM δM 1) :
    QuotientPolynomialEq.QuotientPolynomialForms.toRing R K h I δ hunit L hL
      (formMap R K h I δ hunit L M hL hM hML 1 ω) =
        transition R L M hML (QuotientPolynomialEq.QuotientPolynomialForms.toRing R K h I δ hunit M hM ω) := by
  have hs : Function.Surjective (PD.OneForms.PDOneForms.D R BM IM δM) := fun ω =>
    ⟨QuotientPolynomialMk.QuotientPolynomialPoincare.primitiveForms R K h I δ hunit M hM ω,
      QuotientPolynomialMk.QuotientPolynomialPoincare.differential_primitive R K h I δ hunit M hM ω⟩
  obtain ⟨a, rfl⟩ := hs ω
  rw [formMap_D, QuotientPolynomialEq.QuotientPolynomialForms.toRing_D, QuotientPolynomialEq.QuotientPolynomialForms.toRing_D,
    derivation_transition]

/-- The actual primitives commute with every transition map. -/
theorem primitiveForms_formMap (ω : PD.DeRham.PDDeRham.Form R BM IM δM 1) :
    QuotientPolynomialMk.QuotientPolynomialPoincare.primitiveForms R K h I δ hunit L hL
      (formMap R K h I δ hunit L M hL hM hML 1 ω) =
        transition R L M hML (QuotientPolynomialMk.QuotientPolynomialPoincare.primitiveForms R K h I δ hunit M hM ω) := by
  change QuotientPolynomialMk.QuotientPolynomialPoincare.primitive R K h L
    (QuotientPolynomialEq.QuotientPolynomialForms.toRing R K h I δ hunit L hL
      (formMap R K h I δ hunit L M hL hM hML 1 ω)) = _
  rw [toRing_formMap, primitive_transition]
  rfl

theorem constantCoefficient_transition (a : BM) :
    QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient R K h L (transition R L M hML a) =
      Ideal.Quotient.factorₐ R hML (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient R K h M a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient R K h L (transition R L M hML (qM a)) =
    Ideal.Quotient.factorₐ R hML (QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient R K h M (qM a))
  rw [transition_quotient, QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient_quotient,
    QuotientPolynomialMk.QuotientPolynomialPoincare.constantCoefficient_quotient]
  rfl

theorem constants_transition (a : R ⧸ M) :
    transition R L M hML (QuotientPolynomialMk.QuotientPolynomialPoincare.constants R M a) =
      QuotientPolynomialMk.QuotientPolynomialPoincare.constants R L (Ideal.Quotient.factorₐ R hML a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [QuotientPolynomialMk.QuotientPolynomialPoincare.constants_mk, transition_quotient]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialTransition.QuotientPolynomialTransitions
