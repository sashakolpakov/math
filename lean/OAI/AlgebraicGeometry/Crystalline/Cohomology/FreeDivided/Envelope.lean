import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Universal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp

/-! # Envelope -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope

noncomputable section

/-!
# Free polynomial PD envelopes over arbitrary rings

The relative PD envelope over the zero base ideal of the polynomial coordinates
is isomorphic to the actual free divided-power algebra on those coordinates.
Both inverse maps are constructed by their proved universal properties.
There is no characteristic or torsion-freeness assumption on the base.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R]

local notation "I" => (⊥ : Ideal R)
local notation "δ" => dividedPowersBot R

def polynomialIdeal : Ideal (MvPolynomial σ R) := Multivariable.Envelope.MultivariableEnvelope.polynomialIdeal R σ I

theorem base_le : (I).map (algebraMap R (MvPolynomial σ R)) ≤ polynomialIdeal R σ :=
  Multivariable.Envelope.MultivariableEnvelope.base_le R σ I

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => RingHom.ker (AlgHom.toRingHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation R σ))
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers.FreeDividedPowers.dividedPowers R σ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.polynomialIdeal R σ)
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.polynomialIdeal R σ)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope.polynomialIdeal R σ)

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ)).comp (algebraMap R P)).toAlgebra

def coordinate (i : σ) : E := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ) (MvPolynomial.X i)

def polynomialMap : P →ₐ[R] G := MvPolynomial.aeval (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1)

theorem polynomialMap_C (a : R) : polynomialMap R σ (MvPolynomial.C a) = algebraMap R G a :=
  MvPolynomial.aeval_C (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) a

theorem polynomialMap_X (i : σ) : polynomialMap R σ (MvPolynomial.X i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  MvPolynomial.aeval_X (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) i

theorem bot_isDPMorphism (A : Type u) [CommRing A] (J : Ideal A) (εA : DividedPowers J)
    (f : R →+* A) : DividedPowers.IsDPMorphism δ εA f := by
  constructor
  · rw [Ideal.map_bot]
    exact bot_le
  · intro n a ha
    have ha : a = 0 := ha
    subst a
    by_cases hn : n = 0
    · subst n
      rw [(δ).dpow_zero (Submodule.zero_mem _), map_zero, εA.dpow_zero J.zero_mem, map_one]
    · rw [(δ).dpow_eval_zero hn, map_zero, εA.dpow_eval_zero hn]

def target : PD.EnvelopeDp.PDEnvelope.Target R P I δ (polynomialIdeal R σ) where
  ring := CommRingCat.of G
  algebra := (polynomialMap R σ).toRingHom.toAlgebra
  ideal := IG
  dp := γ
  contains := by
    rw [Ideal.map_le_iff_le_comap, polynomialIdeal, Multivariable.Envelope.MultivariableEnvelope.polynomialIdeal, Ideal.span_le]
    intro a ha
    rcases ha with ⟨a, ha, rfl⟩ | ⟨i, rfl⟩
    · change polynomialMap R σ (MvPolynomial.C a) ∈ IG
      rw [polynomialMap_C]
      have ha : a = 0 := ha
      rw [ha, map_zero]
      exact Submodule.zero_mem _
    · change polynomialMap R σ (MvPolynomial.X i) ∈ IG
      rw [polynomialMap_X]
      exact Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem R σ i
  baseDP := by
    have hc : (polynomialMap R σ).toRingHom.comp (algebraMap R P) = algebraMap R G := by
      ext a
      exact (polynomialMap R σ).commutes a
    change DividedPowers.IsDPMorphism δ γ ((polynomialMap R σ).toRingHom.comp (algebraMap R P))
    rw [hc]
    exact bot_isDPMorphism R G IG γ (algebraMap R G)

def toDivided : E →ₐ[R] G where
  __ := PD.EnvelopeDp.PDEnvelope.evaluate R P I δ (polynomialIdeal R σ) (target R σ)
  commutes' a := (polynomialMap R σ).commutes a

theorem toDivided_ofAlgebra (a : P) :
    toDivided R σ (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ) a) =
      polynomialMap R σ a := rfl

theorem toDivided_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (toDivided R σ).toRingHom :=
  PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R P I δ (polynomialIdeal R σ) (target R σ)

theorem coordinate_mem (i : σ) : coordinate R σ i ∈ IE :=
  PD.EnvelopeDp.PDEnvelope.contains R P I δ (polynomialIdeal R σ)
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Or.inr (Set.mem_range_self i))))

def fromDivided : G →ₐ[R] E :=
  Universal.FreeDividedUniversal.lift R σ E IE ε (coordinate R σ) (coordinate_mem R σ)

theorem fromDivided_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (fromDivided R σ).toRingHom :=
  Universal.FreeDividedUniversal.lift_isDPMorphism R σ E IE ε
    (coordinate R σ) (coordinate_mem R σ)

theorem toDivided_coordinate (i : σ) :
    toDivided R σ (coordinate R σ i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  (toDivided_ofAlgebra R σ (MvPolynomial.X i)).trans (polynomialMap_X R σ i)

theorem fromDivided_coordinate (i : σ) :
    fromDivided R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = coordinate R σ i :=
  Universal.FreeDividedUniversal.lift_coordinate R σ E IE ε
    (coordinate R σ) (coordinate_mem R σ) i

def originalMap : P →ₐ[R] E where
  __ := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ)
  commutes' _ := rfl

theorem fromDivided_comp_polynomialMap :
    (fromDivided R σ).comp (polynomialMap R σ) = originalMap R σ := by
  apply MvPolynomial.algHom_ext
  intro i
  change fromDivided R σ (polynomialMap R σ (MvPolynomial.X i)) = coordinate R σ i
  rw [polynomialMap_X, fromDivided_coordinate]

def roundTrip : E →ₐ[P] E where
  __ := (fromDivided R σ).toRingHom.comp (toDivided R σ).toRingHom
  commutes' a := by
    change fromDivided R σ (toDivided R σ
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ) a)) =
        PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ) a
    rw [toDivided_ofAlgebra]
    exact DFunLike.congr_fun (fromDivided_comp_polynomialMap R σ) a

theorem roundTrip_eq_id : roundTrip R σ = AlgHom.id P E := by
  let T := PD.EnvelopeDp.PDEnvelope.envelopeTarget R P I δ (polynomialIdeal R σ) (base_le R σ)
  have hd : DividedPowers.IsDPMorphism ε ε (roundTrip R σ).toRingHom :=
    (fromDivided_isDPMorphism R σ).comp _ (toDivided_isDPMorphism R σ)
  exact (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ) T _ hd).trans
    (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ) T (AlgHom.id P E)
      (DividedPowers.DPMorphism.id ε).isDPMorphism).symm

theorem fromDivided_toDivided :
    (fromDivided R σ).comp (toDivided R σ) = AlgHom.id R E := by
  apply AlgHom.ext
  intro a
  exact DFunLike.congr_fun (roundTrip_eq_id R σ) a

theorem toDivided_fromDivided :
    (toDivided R σ).comp (fromDivided R σ) = AlgHom.id R G := by
  have hd : DividedPowers.IsDPMorphism γ γ
      ((toDivided R σ).comp (fromDivided R σ)).toRingHom :=
    (toDivided_isDPMorphism R σ).comp _ (fromDivided_isDPMorphism R σ)
  have hX (i : σ) : ((toDivided R σ).comp (fromDivided R σ))
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i := by
    change toDivided R σ (fromDivided R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = _
    rw [fromDivided_coordinate, toDivided_coordinate]
  exact (Universal.FreeDividedUniversal.lift_unique R σ G IG γ
    (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem R σ i)
      _ hd hX).trans
    (Universal.FreeDividedUniversal.lift_unique R σ G IG γ
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem R σ i)
      (AlgHom.id R G) (DividedPowers.DPMorphism.id γ).isDPMorphism (fun _ => rfl)).symm

/-- The actual polynomial PD envelope is the multivariable divided-power algebra. -/
def algebraEquiv : E ≃ₐ[R] G :=
  AlgEquiv.ofAlgHom (toDivided R σ) (fromDivided R σ)
    (toDivided_fromDivided R σ) (fromDivided_toDivided R σ)

theorem algebraEquiv_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (algebraEquiv R σ).toRingHom :=
  toDivided_isDPMorphism R σ

theorem algebraEquiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (algebraEquiv R σ).symm.toRingHom :=
  fromDivided_isDPMorphism R σ

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Envelope.FreeDividedEnvelope
