import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensorNaturality

/-! # Quotient Multivariable To -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableTo.QuotientMultivariableTransitions

noncomputable section

/-!
# Compatible multivariable quotient calculations

Reduction between base ideals preserves divided powers, commutes with
every coordinate derivative and primitive, and respects both the constant
maps and the actual tensor description of the PD form modules.
-/

open _root_.CategoryTheory

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))
  (L M : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ L)
  (hM : DividedPowers.IsSubDPIdeal δ M) (hML : M ≤ L)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.dividedPowers R σ K h I δ hunit
local notation "BL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.Ring R σ L
local notation "BM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.Ring R σ M
local notation "IL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.ideal R σ I L
local notation "IM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.ideal R σ I M
local notation "δL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.dividedPowers R σ K h I δ hunit L hL
local notation "δM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.dividedPowers R σ K h I δ hunit M hM
local notation "qL" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.quotient R σ L
local notation "qM" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.quotient R σ M

def transition : BM →ₐ[R] BL := Ideal.Quotient.factorₐ R (Ideal.map_mono hML)

theorem transition_quotient (a : G) : transition R σ L M hML (qM a) = qL a := rfl

theorem transition_coordinate (i : σ) : transition R σ L M hML (QuotientMultivariableD.QuotientMultivariableForms.coordinate R σ M i) =
    QuotientMultivariableD.QuotientMultivariableForms.coordinate R σ L i := rfl

theorem transition_isDPMorphism :
    DividedPowers.IsDPMorphism δM δL (transition R σ L M hML).toRingHom := by
  apply DividedPowers.IsDPMorphism.of_comp γ δM δL (qM).toRingHom
    (transition R σ L M hML).toRingHom rfl
    (QuotientMultivariableD.QuotientMultivariableForms.quotient_isDPMorphism R σ K h I δ hunit M hM)
  exact QuotientMultivariableD.QuotientMultivariableForms.quotient_isDPMorphism R σ K h I δ hunit L hL

theorem derivation_transition (i : σ) (a : BM) :
    QuotientMultivariableD.QuotientMultivariableForms.derivation R σ K h I δ hunit L i (transition R σ L M hML a) =
      transition R σ L M hML (QuotientMultivariableD.QuotientMultivariableForms.derivation R σ K h I δ hunit M i a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change QuotientMultivariableD.QuotientMultivariableForms.derivation R σ K h I δ hunit L i (transition R σ L M hML (qM a)) =
    transition R σ L M hML (QuotientMultivariableD.QuotientMultivariableForms.derivation R σ K h I δ hunit M i (qM a))
  rw [transition_quotient, QuotientMultivariableD.QuotientMultivariableForms.derivation_quotient,
    QuotientMultivariableD.QuotientMultivariableForms.derivation_quotient, transition_quotient]

theorem primitive_transition (i : σ) (a : BM) :
    QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive R σ K h L i (transition R σ L M hML a) =
      transition R σ L M hML (QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive R σ K h M i a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive R σ K h L i (transition R σ L M hML (qM a)) =
    transition R σ L M hML (QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive R σ K h M i (qM a))
  rw [transition_quotient, QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive_quotient,
    QuotientMultivariableMk.QuotientMultivariablePrimitive.primitive_quotient, transition_quotient]

theorem constantCoefficient_transition (a : BM) :
    QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient R σ K h L (transition R σ L M hML a) =
      Ideal.Quotient.factorₐ R hML (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient R σ K h M a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient R σ K h L (transition R σ L M hML (qM a)) =
    Ideal.Quotient.factorₐ R hML (QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient R σ K h M (qM a))
  rw [transition_quotient, QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient_quotient,
    QuotientMultivariableMk.QuotientMultivariablePrimitive.constantCoefficient_quotient]
  rfl

theorem constants_transition (a : R ⧸ M) :
    transition R σ L M hML (QuotientMultivariableMk.QuotientMultivariablePrimitive.constants R σ M a) =
      QuotientMultivariableMk.QuotientMultivariablePrimitive.constants R σ L (Ideal.Quotient.factorₐ R hML a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [QuotientMultivariableMk.QuotientMultivariablePrimitive.constants_mk, transition_quotient]
  rfl

def formMap (n : ℕ) : PD.DeRham.PDDeRham.Form R BM IM δM n →ₗ[R] PD.DeRham.PDDeRham.Form R BL IL δL n :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (transition R σ L M hML))
    (transition_isDPMorphism R σ K h I δ hunit L M hL hM hML) n

theorem toForms_naturality (n : ℕ) :
    (formMap R σ K h I δ hunit L M hL hM hML n).comp
      ((PD.FormsTensor.PDFormsTensor.toForms R BM σ IM δM (QuotientMultivariableD.QuotientMultivariableForms.coordinate R σ M) n).restrictScalars R) =
        ((PD.FormsTensor.PDFormsTensor.toForms R BL σ IL δL (QuotientMultivariableD.QuotientMultivariableForms.coordinate R σ L) n).restrictScalars R).comp
          (TensorProduct.map (transition R σ L M hML).toLinearMap LinearMap.id) :=
  PD.FormsTensorNaturality.PDFormsTensorNaturality.toForms_naturality R BM BL σ IM IL δM δL
    (QuotientMultivariableD.QuotientMultivariableForms.coordinate R σ M) (QuotientMultivariableD.QuotientMultivariableForms.coordinate R σ L)
    (transition R σ L M hML) (transition_isDPMorphism R σ K h I δ hunit L M hL hM hML)
    (transition_coordinate R σ L M hML) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableTo.QuotientMultivariableTransitions
