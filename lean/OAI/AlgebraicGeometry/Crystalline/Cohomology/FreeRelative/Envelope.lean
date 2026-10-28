import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp

/-! # Envelope -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope

noncomputable section

/-!
# Polynomial PD envelopes in several variables

The relative PD envelope of the base ideal and the polynomial coordinates
is isomorphic to the actual free divided-power algebra on those coordinates.
Both inverse maps are constructed by their proved universal properties.
The result holds over arbitrary PD coefficient rings, including torsion bases.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

def polynomialIdeal : Ideal (MvPolynomial σ R) :=
  Ideal.span ((MvPolynomial.C '' (I : Set R)) ∪ Set.range MvPolynomial.X)

theorem base_le : I.map (algebraMap R (MvPolynomial σ R)) ≤ polynomialIdeal R σ I := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  exact Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩)

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.polynomialIdeal R σ I)
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.polynomialIdeal R σ I)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.polynomialIdeal R σ I)

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I)).comp (algebraMap R P)).toAlgebra

def coordinate (i : σ) : E := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) (MvPolynomial.X i)

def polynomialMap : P →ₐ[R] G := MvPolynomial.aeval (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1)

theorem polynomialMap_C (a : R) : polynomialMap R σ (MvPolynomial.C a) = algebraMap R G a :=
  MvPolynomial.aeval_C (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) a

theorem polynomialMap_X (i : σ) : polynomialMap R σ (MvPolynomial.X i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  MvPolynomial.aeval_X (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) i

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
    exact Powers.FreeRelativePowers.base_isDPMorphism R σ I δ

def toDivided : E →ₐ[R] G where
  __ := PD.EnvelopeDp.PDEnvelope.evaluate R P I δ (polynomialIdeal R σ I) (target R σ I δ)
  commutes' a := (polynomialMap R σ).commutes a

theorem toDivided_ofAlgebra (a : P) :
    toDivided R σ I δ (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) a) =
      polynomialMap R σ a := rfl

theorem toDivided_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (toDivided R σ I δ).toRingHom :=
  PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R P I δ (polynomialIdeal R σ I) (target R σ I δ)

theorem coordinate_mem (i : σ) : coordinate R σ I δ i ∈ IE :=
  PD.EnvelopeDp.PDEnvelope.contains R P I δ (polynomialIdeal R σ I)
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Or.inr (Set.mem_range_self i))))

def fromDivided : G →ₐ[R] E :=
  Universal.FreeRelativeUniversal.lift R σ E IE ε (coordinate R σ I δ) (coordinate_mem R σ I δ)

theorem fromDivided_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (fromDivided R σ I δ).toRingHom :=
  Universal.FreeRelativeUniversal.lift_isDPMorphism R σ I δ E IE ε
    (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism R P I δ (polynomialIdeal R σ I) (base_le R σ I))
    (coordinate R σ I δ) (coordinate_mem R σ I δ)

theorem toDivided_coordinate (i : σ) :
    toDivided R σ I δ (coordinate R σ I δ i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  (toDivided_ofAlgebra R σ I δ (MvPolynomial.X i)).trans (polynomialMap_X R σ i)

theorem fromDivided_coordinate (i : σ) :
    fromDivided R σ I δ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = coordinate R σ I δ i :=
  Universal.FreeRelativeUniversal.lift_coordinate R σ E IE ε
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
  __ := (fromDivided R σ I δ).toRingHom.comp (toDivided R σ I δ).toRingHom
  commutes' a := by
    change fromDivided R σ I δ (toDivided R σ I δ
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) a)) =
        PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I) a
    rw [toDivided_ofAlgebra]
    exact DFunLike.congr_fun (fromDivided_comp_polynomialMap R σ I δ) a

theorem roundTrip_eq_id : roundTrip R σ I δ = AlgHom.id P E := by
  let T := PD.EnvelopeDp.PDEnvelope.envelopeTarget R P I δ (polynomialIdeal R σ I) (base_le R σ I)
  have hd : DividedPowers.IsDPMorphism ε ε (roundTrip R σ I δ).toRingHom :=
    (fromDivided_isDPMorphism R σ I δ).comp _ (toDivided_isDPMorphism R σ I δ)
  exact (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ I) T _ hd).trans
    (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ I) T (AlgHom.id P E)
      (DividedPowers.DPMorphism.id ε).isDPMorphism).symm

theorem fromDivided_toDivided :
    (fromDivided R σ I δ).comp (toDivided R σ I δ) = AlgHom.id R E := by
  apply AlgHom.ext
  intro a
  exact DFunLike.congr_fun (roundTrip_eq_id R σ I δ) a

theorem toDivided_fromDivided :
    (toDivided R σ I δ).comp (fromDivided R σ I δ) = AlgHom.id R G := by
  have hd : DividedPowers.IsDPMorphism γ γ
      ((toDivided R σ I δ).comp (fromDivided R σ I δ)).toRingHom :=
    (toDivided_isDPMorphism R σ I δ).comp _ (fromDivided_isDPMorphism R σ I δ)
  have hX (i : σ) : ((toDivided R σ I δ).comp (fromDivided R σ I δ))
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i := by
    change toDivided R σ I δ (fromDivided R σ I δ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = _
    rw [fromDivided_coordinate, toDivided_coordinate]
  exact (Universal.FreeRelativeUniversal.lift_unique R σ I δ G IG γ
    (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
      _ hd hX).trans
    (Universal.FreeRelativeUniversal.lift_unique R σ I δ G IG γ
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
      (AlgHom.id R G) (DividedPowers.DPMorphism.id γ).isDPMorphism (fun _ => rfl)).symm

/-- The actual polynomial PD envelope is the multivariable divided-power algebra. -/
def algebraEquiv : E ≃ₐ[R] G :=
  AlgEquiv.ofAlgHom (toDivided R σ I δ) (fromDivided R σ I δ)
    (toDivided_fromDivided R σ I δ) (fromDivided_toDivided R σ I δ)

theorem algebraEquiv_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (algebraEquiv R σ I δ).toRingHom :=
  toDivided_isDPMorphism R σ I δ

theorem algebraEquiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (algebraEquiv R σ I δ).symm.toRingHom :=
  fromDivided_isDPMorphism R σ I δ

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope
