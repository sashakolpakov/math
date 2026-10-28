import OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeDerivationsDP
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Envelope One -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeOne.EnvelopeOneForms

noncomputable section

/-!
# One-forms of a divided-power envelope

The PD one-forms of the relative envelope are the scalar extension of
the original algebra's Kähler differentials.
-/

open scoped TensorProduct

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I₀ : Ideal R) (δ₀ : DividedPowers I₀) (I : Ideal A)
  (hbase : I₀.map (algebraMap R A) ≤ I)

local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A I₀ δ₀ I
local notation "Ω" => KaehlerDifferential R A
local notation "Q" => E ⊗[A] Ω
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E J δ 1

variable [Algebra R (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I)]
  [IsScalarTower R A (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I)]

/-- Base-changed universal derivation of the original algebra. -/
def coefficientD : Derivation R A Q :=
  (TensorProduct.mk A E Ω 1).compDer (KaehlerDifferential.D R A)

@[simp] theorem coefficientD_apply (a : A) :
    coefficientD R A I₀ δ₀ I a = (1 : E) ⊗ₜ[A] KaehlerDifferential.D R A a := rfl

/-- The derivation of the envelope with values in the base-changed differentials. -/
def envelopeD : Derivation R E Q :=
  EnvelopeDerivationsDP.EnvelopeDerivations.extend R A I₀ δ₀ I hbase Q (coefficientD R A I₀ δ₀ I)

@[simp] theorem envelopeD_algebraMap (a : A) :
    envelopeD R A I₀ δ₀ I hbase (algebraMap A E a) =
      (1 : E) ⊗ₜ[A] KaehlerDifferential.D R A a := rfl

theorem envelopeD_dpow (n : ℕ) {x : E} (hx : x ∈ J) :
    envelopeD R A I₀ δ₀ I hbase ((δ).dpow (n + 1) x) =
      (δ).dpow n x • envelopeD R A I₀ δ₀ I hbase x :=
  EnvelopeDerivationsDP.EnvelopeDerivations.extend_dpow R A I₀ δ₀ I hbase Q
    (coefficientD R A I₀ δ₀ I) n hx

/-- PD one-forms map to the base change of the original Kähler module. -/
def fromForms : F →ₗ[E] Q :=
  PD.OneForms.PDOneForms.lift R E J δ Q (envelopeD R A I₀ δ₀ I hbase)
    (fun n _ hx => envelopeD_dpow R A I₀ δ₀ I hbase n hx)

@[simp] theorem fromForms_D (x : E) :
    fromForms R A I₀ δ₀ I hbase (PD.OneForms.PDOneForms.D R E J δ x) =
      envelopeD R A I₀ δ₀ I hbase x :=
  PD.OneForms.PDOneForms.lift_D R E J δ Q (envelopeD R A I₀ δ₀ I hbase) _ x

/-- The canonical map from base-changed Kähler forms to PD forms. -/
def toForms : Q →ₗ[E] F :=
  ((PD.OneForms.PDOneForms.D R E J δ).compAlgebraMap A).liftKaehlerDifferential.liftBaseChange E

@[simp] theorem toForms_tmul_D (a : E) (b : A) :
    toForms R A I₀ δ₀ I (a ⊗ₜ[A] KaehlerDifferential.D R A b) =
      a • PD.OneForms.PDOneForms.D R E J δ (algebraMap A E b) := by
  change ((PD.OneForms.PDOneForms.D R E J δ).compAlgebraMap A).liftKaehlerDifferential.liftBaseChange E
    (a ⊗ₜ[A] KaehlerDifferential.D R A b) = _
  rw [LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

theorem fromForms_toForms :
    (fromForms R A I₀ δ₀ I hbase).comp (toForms R A I₀ δ₀ I) = LinearMap.id := by
  apply (LinearMap.liftBaseChangeEquiv E).symm.injective
  apply Derivation.liftKaehlerDifferential_unique (R := R)
  apply Derivation.ext
  intro a
  change fromForms R A I₀ δ₀ I hbase
    (toForms R A I₀ δ₀ I ((1 : E) ⊗ₜ[A] KaehlerDifferential.D R A a)) =
      (1 : E) ⊗ₜ[A] KaehlerDifferential.D R A a
  rw [toForms_tmul_D, one_smul, fromForms_D, envelopeD_algebraMap]

theorem toForms_envelopeD :
    (toForms R A I₀ δ₀ I).compDer (envelopeD R A I₀ δ₀ I hbase) =
      PD.OneForms.PDOneForms.D R E J δ := by
  apply EnvelopeDerivationsDP.EnvelopeDerivations.derivation_ext R A I₀ δ₀ I hbase F
  · intro a
    change toForms R A I₀ δ₀ I (envelopeD R A I₀ δ₀ I hbase (algebraMap A E a)) = _
    rw [envelopeD_algebraMap, toForms_tmul_D, one_smul]
  · intro n x hx
    change toForms R A I₀ δ₀ I (envelopeD R A I₀ δ₀ I hbase ((δ).dpow (n + 1) x)) = _
    rw [envelopeD_dpow R A I₀ δ₀ I hbase n hx, map_smul]
    rfl
  · intro n x hx
    exact PD.OneForms.PDOneForms.D_dpow R E J δ n hx

theorem toForms_fromForms :
    (toForms R A I₀ δ₀ I).comp (fromForms R A I₀ δ₀ I hbase) = LinearMap.id := by
  apply PD.OneForms.PDOneForms.linearMap_ext R E J δ F
  intro x
  change toForms R A I₀ δ₀ I (fromForms R A I₀ δ₀ I hbase (PD.OneForms.PDOneForms.D R E J δ x)) = _
  rw [fromForms_D]
  exact DFunLike.congr_fun (toForms_envelopeD R A I₀ δ₀ I hbase) x

/-- PD one-forms of the envelope are exactly the base-changed Kähler differentials. -/
def formsEquiv : Q ≃ₗ[E] F :=
  LinearEquiv.ofLinearMap (toForms R A I₀ δ₀ I) (fromForms R A I₀ δ₀ I hbase)
    (toForms_fromForms R A I₀ δ₀ I hbase) (fromForms_toForms R A I₀ δ₀ I hbase)

@[simp] theorem formsEquiv_tmul_D (a : E) (b : A) :
    formsEquiv R A I₀ δ₀ I hbase (a ⊗ₜ[A] KaehlerDifferential.D R A b) =
      a • PD.OneForms.PDOneForms.D R E J δ (algebraMap A E b) :=
  toForms_tmul_D R A I₀ δ₀ I a b

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeOne.EnvelopeOneForms
