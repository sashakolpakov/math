import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp

/-! # Shifted Polynomial DP -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialDP.ShiftedPolynomialEnvelope

noncomputable section

/-!
# Polynomial PD envelopes around specified coordinate lifts

The relative PD envelope of the base ideal and the differences between
polynomial coordinates and specified base-ring lifts
is isomorphic to the actual free divided-power algebra on those coordinates.
Both inverse maps are constructed by their proved universal properties.
The result holds over arbitrary PD coefficient rings, including torsion bases.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I) (x : σ → R)

def polynomialIdeal : Ideal (MvPolynomial σ R) :=
  Ideal.span ((MvPolynomial.C '' (I : Set R)) ∪ Set.range (fun i => MvPolynomial.X i - MvPolynomial.C (x i)))

theorem base_le : I.map (algebraMap R (MvPolynomial σ R)) ≤ polynomialIdeal R σ I x := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  exact Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩)

local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x)
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x)

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x)).comp (algebraMap R P)).toAlgebra

def coordinate (i : σ) : E := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x) (MvPolynomial.X i - MvPolynomial.C (x i))

def polynomialMap : P →ₐ[R] G := MvPolynomial.aeval (fun i => algebraMap R G (x i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)

theorem polynomialMap_C (a : R) : polynomialMap R σ x (MvPolynomial.C a) = algebraMap R G a :=
  MvPolynomial.aeval_C (fun i => algebraMap R G (x i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) a

theorem polynomialMap_X (i : σ) : polynomialMap R σ x (MvPolynomial.X i) = algebraMap R G (x i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  MvPolynomial.aeval_X (fun i => algebraMap R G (x i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) i

def target : PD.EnvelopeDp.PDEnvelope.Target R P I δ (polynomialIdeal R σ I x) where
  ring := CommRingCat.of G
  algebra := (polynomialMap R σ x).toRingHom.toAlgebra
  ideal := IG
  dp := γ
  contains := by
    rw [Ideal.map_le_iff_le_comap, polynomialIdeal, Ideal.span_le]
    intro a ha
    rcases ha with ⟨a, ha, rfl⟩ | ⟨i, rfl⟩
    · change polynomialMap R σ x (MvPolynomial.C a) ∈ IG
      rw [polynomialMap_C]
      exact Ideal.subset_span (Or.inl ⟨⟨a, ha⟩, rfl⟩)
    · change polynomialMap R σ x (MvPolynomial.X i - MvPolynomial.C (x i)) ∈ IG
      rw [map_sub, polynomialMap_X, polynomialMap_C, add_sub_cancel_left]
      exact Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero
  baseDP := by
    have hc : (polynomialMap R σ x).toRingHom.comp (algebraMap R P) = algebraMap R G := by
      ext a
      exact (polynomialMap R σ x).commutes a
    change DividedPowers.IsDPMorphism δ γ ((polynomialMap R σ x).toRingHom.comp (algebraMap R P))
    rw [hc]
    exact FreeRelative.Powers.FreeRelativePowers.base_isDPMorphism R σ I δ

def toDivided : E →ₐ[R] G where
  __ := PD.EnvelopeDp.PDEnvelope.evaluate R P I δ (polynomialIdeal R σ I x) (target R σ I δ x)
  commutes' a := (polynomialMap R σ x).commutes a

theorem toDivided_ofAlgebra (a : P) :
    toDivided R σ I δ x (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x) a) =
      polynomialMap R σ x a := rfl

theorem toDivided_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (toDivided R σ I δ x).toRingHom :=
  PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R P I δ (polynomialIdeal R σ I x) (target R σ I δ x)

theorem coordinate_mem (i : σ) : coordinate R σ I δ x i ∈ IE :=
  PD.EnvelopeDp.PDEnvelope.contains R P I δ (polynomialIdeal R σ I x)
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Or.inr (Set.mem_range_self i))))

def fromDivided : G →ₐ[R] E :=
  FreeRelative.Universal.FreeRelativeUniversal.lift R σ E IE ε (coordinate R σ I δ x) (coordinate_mem R σ I δ x)

theorem fromDivided_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (fromDivided R σ I δ x).toRingHom :=
  FreeRelative.Universal.FreeRelativeUniversal.lift_isDPMorphism R σ I δ E IE ε
    (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism R P I δ (polynomialIdeal R σ I x) (base_le R σ I x))
    (coordinate R σ I δ x) (coordinate_mem R σ I δ x)

theorem toDivided_coordinate (i : σ) :
    toDivided R σ I δ x (coordinate R σ I δ x i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i := by
  change polynomialMap R σ x (MvPolynomial.X i - MvPolynomial.C (x i)) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i
  rw [map_sub, polynomialMap_X, polynomialMap_C, add_sub_cancel_left]

theorem fromDivided_coordinate (i : σ) :
    fromDivided R σ I δ x (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = coordinate R σ I δ x i :=
  FreeRelative.Universal.FreeRelativeUniversal.lift_coordinate R σ E IE ε
    (coordinate R σ I δ x) (coordinate_mem R σ I δ x) i

def originalMap : P →ₐ[R] E where
  __ := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x)
  commutes' _ := rfl

theorem fromDivided_comp_polynomialMap :
    (fromDivided R σ I δ x).comp (polynomialMap R σ x) = originalMap R σ I δ x := by
  apply MvPolynomial.algHom_ext
  intro i
  change fromDivided R σ I δ x (polynomialMap R σ x (MvPolynomial.X i)) =
    PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x) (MvPolynomial.X i)
  rw [polynomialMap_X, map_add, AlgHom.commutes, fromDivided_coordinate]
  change algebraMap R E (x i) +
    PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x) (MvPolynomial.X i - MvPolynomial.C (x i)) = _
  rw [map_sub]
  change algebraMap R E (x i) +
    (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x) (MvPolynomial.X i) - algebraMap R E (x i)) = _
  rw [← add_sub_assoc, add_sub_cancel_left]

def roundTrip : E →ₐ[P] E where
  __ := (fromDivided R σ I δ x).toRingHom.comp (toDivided R σ I δ x).toRingHom
  commutes' a := by
    change fromDivided R σ I δ x (toDivided R σ I δ x
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x) a)) =
        PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R σ I x) a
    rw [toDivided_ofAlgebra]
    exact DFunLike.congr_fun (fromDivided_comp_polynomialMap R σ I δ x) a

theorem roundTrip_eq_id : roundTrip R σ I δ x = AlgHom.id P E := by
  let T := PD.EnvelopeDp.PDEnvelope.envelopeTarget R P I δ (polynomialIdeal R σ I x) (base_le R σ I x)
  have hd : DividedPowers.IsDPMorphism ε ε (roundTrip R σ I δ x).toRingHom :=
    (fromDivided_isDPMorphism R σ I δ x).comp _ (toDivided_isDPMorphism R σ I δ x)
  exact (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ I x) T _ hd).trans
    (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R σ I x) T (AlgHom.id P E)
      (DividedPowers.DPMorphism.id ε).isDPMorphism).symm

theorem fromDivided_toDivided :
    (fromDivided R σ I δ x).comp (toDivided R σ I δ x) = AlgHom.id R E := by
  apply AlgHom.ext
  intro a
  exact DFunLike.congr_fun (roundTrip_eq_id R σ I δ x) a

theorem toDivided_fromDivided :
    (toDivided R σ I δ x).comp (fromDivided R σ I δ x) = AlgHom.id R G := by
  have hd : DividedPowers.IsDPMorphism γ γ
      ((toDivided R σ I δ x).comp (fromDivided R σ I δ x)).toRingHom :=
    (toDivided_isDPMorphism R σ I δ x).comp _ (fromDivided_isDPMorphism R σ I δ x)
  have hX (i : σ) : ((toDivided R σ I δ x).comp (fromDivided R σ I δ x))
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i := by
    change toDivided R σ I δ x (fromDivided R σ I δ x (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = _
    rw [fromDivided_coordinate, toDivided_coordinate]
  exact (FreeRelative.Universal.FreeRelativeUniversal.lift_unique R σ I δ G IG γ
    (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
      _ hd hX).trans
    (FreeRelative.Universal.FreeRelativeUniversal.lift_unique R σ I δ G IG γ
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) (fun i => Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero)
      (AlgHom.id R G) (DividedPowers.DPMorphism.id γ).isDPMorphism (fun _ => rfl)).symm

/-- The actual polynomial PD envelope is the multivariable divided-power algebra. -/
def algebraEquiv : E ≃ₐ[R] G :=
  AlgEquiv.ofAlgHom (toDivided R σ I δ x) (fromDivided R σ I δ x)
    (toDivided_fromDivided R σ I δ x) (fromDivided_toDivided R σ I δ x)

theorem algebraEquiv_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (algebraEquiv R σ I δ x).toRingHom :=
  toDivided_isDPMorphism R σ I δ x

theorem algebraEquiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (algebraEquiv R σ I δ x).symm.toRingHom :=
  fromDivided_isDPMorphism R σ I δ x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialDP.ShiftedPolynomialEnvelope
