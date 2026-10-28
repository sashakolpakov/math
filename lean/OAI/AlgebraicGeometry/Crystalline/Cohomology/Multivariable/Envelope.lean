import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp

/-! # Envelope -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope

noncomputable section

/-!
# Polynomial PD envelopes in several variables

The relative PD envelope of the base ideal and the polynomial coordinates
is isomorphic to the actual free divided-power algebra on those coordinates.
Both inverse maps are constructed by their proved universal properties.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

def polynomialIdeal : Ideal (MvPolynomial σ R) :=
  Ideal.span ((MvPolynomial.C '' (I : Set R)) ∪ Set.range MvPolynomial.X)

theorem base_le : I.map (algebraMap R (MvPolynomial σ R)) ≤ polynomialIdeal R σ I := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  exact Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩)

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.dividedPowers R σ K h I δ hunit
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.polynomialIdeal R σ I)
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.polynomialIdeal R σ I)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope.polynomialIdeal R σ I)

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I)).comp (algebraMap R P)).toAlgebra

def coordinate (i : σ) : E := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) (MvPolynomial.X i)

def polynomialMap : P →ₐ[R] G := MvPolynomial.aeval (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1)

theorem polynomialMap_C (a : R) : polynomialMap R σ (MvPolynomial.C a) = algebraMap R G a :=
  MvPolynomial.aeval_C (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) a

theorem polynomialMap_X (i : σ) : polynomialMap R σ (MvPolynomial.X i) = DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  MvPolynomial.aeval_X (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) i

def target : PD.EnvelopeDp.PDEnvelope.Target R P I δ (polynomialIdeal R σ I) where
  ring := CommRingCat.of G
  algebra := (polynomialMap R σ).toRingHom.toAlgebra
  ideal := IG
  dp := γ
  contains := by
    rw [Ideal.map_le_iff_le_comap, polynomialIdeal, Ideal.span_le]
    intro a ha
    rcases ha with ⟨a, ha, rfl⟩ | ⟨i, rfl⟩
    · change polynomialMap R σ (MvPolynomial.C a) ∈ IG
      rw [polynomialMap_C]
      exact Ideal.subset_span (Or.inl ⟨⟨a, ha⟩, rfl⟩)
    · change polynomialMap R σ (MvPolynomial.X i) ∈ IG
      rw [polynomialMap_X]
      exact Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero
  baseDP := by
    have hc : (polynomialMap R σ).toRingHom.comp (algebraMap R P) = algebraMap R G := by
      ext a
      exact (polynomialMap R σ).commutes a
    change DividedPowers.IsDPMorphism δ γ ((polynomialMap R σ).toRingHom.comp (algebraMap R P))
    rw [hc]
    exact Multivariable.DividedPowers.MultivariableDividedPowers.base_isDPMorphism R σ K h I δ hunit

def toDivided : E →ₐ[R] G where
  __ := PD.EnvelopeDp.PDEnvelope.evaluate R P I δ (polynomialIdeal R σ I) (target R σ K h I δ hunit)
  commutes' a := (polynomialMap R σ).commutes a

theorem toDivided_ofAlgebra (a : P) :
    toDivided R σ K h I δ hunit (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) a) =
      polynomialMap R σ a := rfl

theorem toDivided_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (toDivided R σ K h I δ hunit).toRingHom :=
  PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R P I δ (polynomialIdeal R σ I) (target R σ K h I δ hunit)

theorem coordinate_mem (i : σ) : coordinate R σ I δ i ∈ IE :=
  PD.EnvelopeDp.PDEnvelope.contains R P I δ (polynomialIdeal R σ I)
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Or.inr (Set.mem_range_self i))))

def fromDivided : G →ₐ[R] E :=
  DividedUniversal.MultivariableDividedUniversal.lift R σ E IE ε (coordinate R σ I δ) (coordinate_mem R σ I δ)

theorem fromDivided_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (fromDivided R σ I δ).toRingHom :=
  DividedUniversal.MultivariableDividedUniversal.lift_isDPMorphism R σ K h I δ hunit E IE ε
    (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism R P I δ (polynomialIdeal R σ I) (base_le R σ I))
    (coordinate R σ I δ) (coordinate_mem R σ I δ)

theorem toDivided_coordinate (i : σ) :
    toDivided R σ K h I δ hunit (coordinate R σ I δ i) = DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  (toDivided_ofAlgebra R σ K h I δ hunit (MvPolynomial.X i)).trans (polynomialMap_X R σ i)

theorem fromDivided_coordinate (i : σ) :
    fromDivided R σ I δ (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = coordinate R σ I δ i :=
  DividedUniversal.MultivariableDividedUniversal.lift_coordinate R σ E IE ε
    (coordinate R σ I δ) (coordinate_mem R σ I δ) i

def originalMap : P →ₐ[R] E where
  __ := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I)
  commutes' _ := rfl

theorem fromDivided_comp_polynomialMap :
    (fromDivided R σ I δ).comp (polynomialMap R σ) = originalMap R σ I δ := by
  apply MvPolynomial.algHom_ext
  intro i
  change fromDivided R σ I δ (polynomialMap R σ (MvPolynomial.X i)) = coordinate R σ I δ i
  rw [polynomialMap_X, fromDivided_coordinate]

def roundTrip : E →ₐ[P] E where
  __ := (fromDivided R σ I δ).toRingHom.comp (toDivided R σ K h I δ hunit).toRingHom
  commutes' a := by
    change fromDivided R σ I δ (toDivided R σ K h I δ hunit
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) a)) =
        PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) a
    rw [toDivided_ofAlgebra]
    exact DFunLike.congr_fun (fromDivided_comp_polynomialMap R σ I δ) a

theorem roundTrip_eq_id : roundTrip R σ K h I δ hunit = AlgHom.id P E := by
  let T := PD.EnvelopeDp.PDEnvelope.envelopeTarget R P I δ (polynomialIdeal R σ I) (base_le R σ I)
  have hd : DividedPowers.IsDPMorphism ε ε (roundTrip R σ K h I δ hunit).toRingHom :=
    (fromDivided_isDPMorphism R σ K h I δ hunit).comp _ (toDivided_isDPMorphism R σ K h I δ hunit)
  exact (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ I) T _ hd).trans
    (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ I) T (AlgHom.id P E)
      (DividedPowers.DPMorphism.id ε).isDPMorphism).symm

theorem fromDivided_toDivided :
    (fromDivided R σ I δ).comp (toDivided R σ K h I δ hunit) = AlgHom.id R E := by
  apply AlgHom.ext
  intro a
  exact DFunLike.congr_fun (roundTrip_eq_id R σ K h I δ hunit) a

theorem toDivided_fromDivided :
    (toDivided R σ K h I δ hunit).comp (fromDivided R σ I δ) = AlgHom.id R G := by
  have hd : DividedPowers.IsDPMorphism γ γ
      ((toDivided R σ K h I δ hunit).comp (fromDivided R σ I δ)).toRingHom :=
    (toDivided_isDPMorphism R σ K h I δ hunit).comp _ (fromDivided_isDPMorphism R σ K h I δ hunit)
  have hX (i : σ) : ((toDivided R σ K h I δ hunit).comp (fromDivided R σ I δ))
      (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i := by
    change toDivided R σ K h I δ hunit (fromDivided R σ I δ (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = _
    rw [fromDivided_coordinate, toDivided_coordinate]
  exact (DividedUniversal.MultivariableDividedUniversal.lift_unique R σ K h I δ hunit G IG γ
    (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
      _ hd hX).trans
    (DividedUniversal.MultivariableDividedUniversal.lift_unique R σ K h I δ hunit G IG γ
      (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
      (AlgHom.id R G) (DividedPowers.DPMorphism.id γ).isDPMorphism (fun _ => rfl)).symm

/-- The actual polynomial PD envelope is the multivariable divided-power algebra. -/
def algebraEquiv : E ≃ₐ[R] G :=
  AlgEquiv.ofAlgHom (toDivided R σ K h I δ hunit) (fromDivided R σ I δ)
    (toDivided_fromDivided R σ K h I δ hunit) (fromDivided_toDivided R σ K h I δ hunit)

theorem algebraEquiv_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (algebraEquiv R σ K h I δ hunit).toRingHom :=
  toDivided_isDPMorphism R σ K h I δ hunit

theorem algebraEquiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (algebraEquiv R σ K h I δ hunit).symm.toRingHom :=
  fromDivided_isDPMorphism R σ K h I δ hunit

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Envelope.MultivariableEnvelope
