import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Envelope -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope

noncomputable section

/-!
# Identifying the polynomial PD envelope with the divided-polynomial algebra

Both maps are constructed by their proved universal properties. This
links the integral local Poincaré calculation to the actual envelopes
used in crystalline frames.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra

universe u

variable (R K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

def polynomialIdeal : Ideal (Polynomial R) :=
  Ideal.span ((Polynomial.C '' (I : Set R)) ∪ {Polynomial.X})

theorem base_le : I.map (algebraMap R (Polynomial R)) ≤ polynomialIdeal R I := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  exact Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩)

local notation "P" => Polynomial R
local notation "G" => DividedPowerAlgebra R R
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal R I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers R K h I δ hunit
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.polynomialIdeal R I)
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.polynomialIdeal R I)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.polynomialIdeal R I)
local notation "XG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.monomial R 1
local notation "XE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope.polynomialIdeal R I) Polynomial.X

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R I)).comp (algebraMap R P)).toAlgebra

def polynomialMap : P →ₐ[R] G := Polynomial.aeval XG

@[simp] theorem polynomialMap_C (a : R) : polynomialMap R (Polynomial.C a) = algebraMap R G a :=
  Polynomial.aeval_C XG a

@[simp] theorem polynomialMap_X : polynomialMap R Polynomial.X = XG := Polynomial.aeval_X XG

/-- The divided-polynomial algebra is a target of the relative envelope. -/
def target : PD.EnvelopeDp.PDEnvelope.Target R P I δ (polynomialIdeal R I) where
  ring := CommRingCat.of G
  algebra := (polynomialMap R).toRingHom.toAlgebra
  ideal := IG
  dp := γ
  contains := by
    rw [Ideal.map_le_iff_le_comap, polynomialIdeal, Ideal.span_le]
    intro a ha
    rcases ha with ⟨a, ha, rfl⟩ | (rfl : a = Polynomial.X)
    · change polynomialMap R (Polynomial.C a) ∈ IG
      rw [polynomialMap_C]
      exact Ideal.subset_span (Or.inl ⟨⟨a, ha⟩, rfl⟩)
    · change polynomialMap R Polynomial.X ∈ IG
      rw [polynomialMap_X]
      exact Divided.PolynomialOneForms.DividedPolynomialOneForms.variable_mem R I
  baseDP := by
    have hc : (polynomialMap R).toRingHom.comp (algebraMap R P) = algebraMap R G := by
      ext a
      exact (polynomialMap R).commutes a
    change DividedPowers.IsDPMorphism δ γ ((polynomialMap R).toRingHom.comp (algebraMap R P))
    rw [hc]
    exact Divided.PolynomialPowers.DividedPolynomialPowers.base_isDPMorphism R K h I δ hunit

/-- Map the universal envelope to the explicit divided-polynomial algebra. -/
def toPolynomial : E →ₐ[R] G where
  __ := PD.EnvelopeDp.PDEnvelope.evaluate R P I δ (polynomialIdeal R I) (target R K h I δ hunit)
  commutes' a := (polynomialMap R).commutes a

theorem toPolynomial_ofAlgebra (a : P) :
    toPolynomial R K h I δ hunit (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R I) a) =
      polynomialMap R a := rfl

theorem toPolynomial_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (toPolynomial R K h I δ hunit).toRingHom :=
  PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R P I δ (polynomialIdeal R I) (target R K h I δ hunit)

theorem variable_mem : XE ∈ IE :=
  PD.EnvelopeDp.PDEnvelope.contains R P I δ (polynomialIdeal R I)
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Or.inr (Set.mem_singleton Polynomial.X))))

/-- Map the explicit divided-polynomial algebra back to the universal envelope. -/
def fromPolynomial : G →ₐ[R] E :=
  Divided.PolynomialUniversal.DividedPolynomialUniversal.lift R E IE ε XE (variable_mem R I δ)

theorem fromPolynomial_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (fromPolynomial R I δ).toRingHom :=
  Divided.PolynomialUniversal.DividedPolynomialUniversal.lift_isDPMorphism R K h I δ hunit E IE ε
    (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism R P I δ (polynomialIdeal R I) (base_le R I))
    XE (variable_mem R I δ)

@[simp] theorem toPolynomial_variable : toPolynomial R K h I δ hunit XE = XG :=
  (toPolynomial_ofAlgebra R K h I δ hunit Polynomial.X).trans (polynomialMap_X R)

@[simp] theorem fromPolynomial_variable : fromPolynomial R I δ XG = XE :=
  Divided.PolynomialUniversal.DividedPolynomialUniversal.lift_variable R E IE ε XE (variable_mem R I δ)

def originalMap : P →ₐ[R] E where
  __ := PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R I)
  commutes' _ := rfl

theorem fromPolynomial_comp_polynomialMap :
    (fromPolynomial R I δ).comp (polynomialMap R) = originalMap R I δ := by
  apply Polynomial.algHom_ext
  change fromPolynomial R I δ (polynomialMap R Polynomial.X) = XE
  rw [polynomialMap_X, fromPolynomial_variable]

def roundTrip : E →ₐ[P] E where
  __ := (fromPolynomial R I δ).toRingHom.comp (toPolynomial R K h I δ hunit).toRingHom
  commutes' a := by
    change fromPolynomial R I δ (toPolynomial R K h I δ hunit
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R I) a)) =
        PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (polynomialIdeal R I) a
    rw [toPolynomial_ofAlgebra]
    exact DFunLike.congr_fun (fromPolynomial_comp_polynomialMap R I δ) a

theorem roundTrip_eq_id : roundTrip R K h I δ hunit = AlgHom.id P E := by
  let T := PD.EnvelopeDp.PDEnvelope.envelopeTarget R P I δ (polynomialIdeal R I) (base_le R I)
  have hd : DividedPowers.IsDPMorphism ε ε (roundTrip R K h I δ hunit).toRingHom :=
    (fromPolynomial_isDPMorphism R K h I δ hunit).comp _ (toPolynomial_isDPMorphism R K h I δ hunit)
  exact (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R I) T _ hd).trans
    (PD.EnvelopeDp.PDEnvelope.lift_unique R P I δ (polynomialIdeal R I) T (AlgHom.id P E)
      (DividedPowers.DPMorphism.id ε).isDPMorphism).symm

theorem fromPolynomial_toPolynomial :
    (fromPolynomial R I δ).comp (toPolynomial R K h I δ hunit) = AlgHom.id R E := by
  apply AlgHom.ext
  intro x
  exact DFunLike.congr_fun (roundTrip_eq_id R K h I δ hunit) x

theorem toPolynomial_fromPolynomial :
    (toPolynomial R K h I δ hunit).comp (fromPolynomial R I δ) = AlgHom.id R G := by
  have hd : DividedPowers.IsDPMorphism γ γ
      ((toPolynomial R K h I δ hunit).comp (fromPolynomial R I δ)).toRingHom :=
    (toPolynomial_isDPMorphism R K h I δ hunit).comp _ (fromPolynomial_isDPMorphism R K h I δ hunit)
  have hX : ((toPolynomial R K h I δ hunit).comp (fromPolynomial R I δ)) XG = XG := by
    change toPolynomial R K h I δ hunit (fromPolynomial R I δ XG) = XG
    rw [fromPolynomial_variable, toPolynomial_variable]
  exact (Divided.PolynomialUniversal.DividedPolynomialUniversal.lift_unique R K h I δ hunit G IG γ XG
    (Divided.PolynomialOneForms.DividedPolynomialOneForms.variable_mem R I) _ hd hX).trans
    (Divided.PolynomialUniversal.DividedPolynomialUniversal.lift_unique R K h I δ hunit G IG γ XG
      (Divided.PolynomialOneForms.DividedPolynomialOneForms.variable_mem R I) (AlgHom.id R G)
      (DividedPowers.DPMorphism.id γ).isDPMorphism rfl).symm

/-- The universal polynomial PD envelope is the explicit divided-polynomial algebra. -/
def algebraEquiv : E ≃ₐ[R] G :=
  AlgEquiv.ofAlgHom (toPolynomial R K h I δ hunit) (fromPolynomial R I δ)
    (toPolynomial_fromPolynomial R K h I δ hunit) (fromPolynomial_toPolynomial R K h I δ hunit)

theorem algebraEquiv_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (algebraEquiv R K h I δ hunit).toRingHom :=
  toPolynomial_isDPMorphism R K h I δ hunit

theorem algebraEquiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (algebraEquiv R K h I δ hunit).symm.toRingHom :=
  fromPolynomial_isDPMorphism R K h I δ hunit

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Envelope.PolynomialEnvelope
