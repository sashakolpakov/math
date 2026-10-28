import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ActualLiftRing
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing

namespace OAI.Algorithms

/-!
# Arbitrary-degree ternary unramified counting rings

This semantic model reuses the audited monic-lift construction. The extension
is not restricted to degree four. Its finite coefficient representation and
exact readback are exposed separately from any machine-cost refinement.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingCore

open Polynomial

instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev Base (t : ℕ) := LiftRing.Base 3 t
abbrev E (d : ℕ) := FiniteField.E 3 d
abbrev O (d t : ℕ) := ActualLiftRing.Ring 3 d t
abbrev definingPolynomial (d t : ℕ) := ActualLiftRing.chosenF 3 d t

variable (d t : ℕ)

def rho (ht : 0 < t) : O d t →+* E d := ActualLiftRing.rho 3 d t ht

theorem rho_surjective (ht : 0 < t) : Function.Surjective (rho d t ht) :=
  ActualLiftRing.rho_surjective 3 d t ht

theorem rho_eq_zero_iff (ht : 0 < t) (x : O d t) :
    rho d t ht x = 0 ↔ (3 : O d t) ∣ x :=
  ActualLiftRing.rho_eq_zero_iff 3 d t ht x

theorem rho_ker (ht : 0 < t) :
    RingHom.ker (rho d t ht) = Ideal.span ({(3 : O d t)} : Set (O d t)) :=
  ActualLiftRing.rho_ker 3 d t ht

theorem prime_power_zero : (3 : O d t) ^ t = 0 :=
  ActualLiftRing.prime_power_zero 3 d t

theorem pow_eq_zero_of_rho_eq_zero (ht : 0 < t) {x : O d t}
    (hx : rho d t ht x = 0) : x ^ t = 0 := by
  obtain ⟨a, rfl⟩ := (rho_eq_zero_iff d t ht x).mp hx
  rw [mul_pow, prime_power_zero, zero_mul]

theorem isUnit_of_rho_ne_zero (ht : 0 < t) {x : O d t}
    (hx : rho d t ht x ≠ 0) : IsUnit x :=
  NilpotentDefect.isUnit_of_residue_ne_zero
    (rho d t ht) (rho_surjective d t ht) (3 : O d t) t
    (prime_power_zero d t) (fun z hz => (rho_eq_zero_iff d t ht z).mp hz) hx

theorem isUnit_iff_rho_ne_zero (ht : 0 < t) (x : O d t) :
    IsUnit x ↔ rho d t ht x ≠ 0 := by
  constructor
  · intro hx
    exact (hx.map (rho d t ht)).ne_zero
  · exact isUnit_of_rho_ne_zero d t ht

/-- The base ring embeds as constant polynomials. -/
def base : Base t →+* O d t := LiftRing.of (definingPolynomial d t)

theorem polynomial_monic (ht : 0 < t) : (definingPolynomial d t).Monic :=
  ActualLiftRing.F_monic 3 d t ht

theorem polynomial_degree (ht : 0 < t) (hd : d ≠ 0) :
    (definingPolynomial d t).natDegree = d := ActualLiftRing.F_degree 3 d t ht hd

theorem base_injective (ht : 0 < t) (hd : d ≠ 0) : Function.Injective (base d t) :=
  LiftRing.base_injective (polynomial_monic d t ht)
    (by rw [polynomial_degree d t ht hd]; exact Nat.pos_of_ne_zero hd)

/-- The exact finite power-basis coordinate representation. -/
def coordinates (ht : 0 < t) (hd : d ≠ 0) : O d t ≃ₗ[Base t] (Fin d → Base t) :=
  SubexpActualRing.coordinatesOfDegree (definingPolynomial d t)
    (polynomial_monic d t ht) (polynomial_degree d t ht hd)

@[simp] theorem coordinates_apply (ht : 0 < t) (hd : d ≠ 0)
    (x : O d t) (i : Fin d) :
    coordinates d t ht hd x i = (LiftRing.remainder (polynomial_monic d t ht) x).coeff i :=
  SubexpActualRing.coordinatesOfDegree_apply _ _ _ x i

@[simp] theorem coordinates_symm_apply (ht : 0 < t) (hd : d ≠ 0)
    (a : Fin d → Base t) :
    (coordinates d t ht hd).symm a =
      LiftRing.mk (definingPolynomial d t) (∑ i : Fin d, monomial i (a i)) :=
  SubexpActualRing.coordinatesOfDegree_symm_apply _ _ _ a

theorem coordinates_base (ht : 0 < t) (hd : d ≠ 0) (a : Base t) (i : Fin d) :
    coordinates d t ht hd (base d t a) i = (C a).coeff i := by
  rw [coordinates_apply]
  change (LiftRing.remainder (polynomial_monic d t ht)
    (LiftRing.of (definingPolynomial d t) a)).coeff i = _
  rw [LiftRing.remainder_of _ (by rw [polynomial_degree d t ht hd]; omega)]

theorem finite_type (ht : 0 < t) : Finite (O d t) :=
  LiftRing.extension_finite_type (polynomial_monic d t ht)

theorem free_module (ht : 0 < t) : Module.Free (Base t) (O d t) :=
  LiftRing.extension_free (polynomial_monic d t ht)

theorem finite_module (ht : 0 < t) : Module.Finite (Base t) (O d t) :=
  LiftRing.extension_finite (polynomial_monic d t ht)

theorem cardinality (ht : 0 < t) (hd : d ≠ 0) : Nat.card (O d t) = (3 ^ t) ^ d := by
  simpa only [polynomial_degree d t ht hd] using
    LiftRing.natCard_lambda 3 t (polynomial_monic d t ht)

theorem residue_cardinality (hd : d ≠ 0) : Nat.card (E d) = 3 ^ d :=
  FiniteField.extension_natCard 3 d hd

/-- Read the constant coordinate; it is an exact left inverse on the base ring. -/
def readBase (ht : 0 < t) (x : O d t) : Base t :=
  (LiftRing.remainder (polynomial_monic d t ht) x).coeff 0

@[simp] theorem readBase_base (ht : 0 < t) (hd : d ≠ 0) (a : Base t) :
    readBase d t ht (base d t a) = a := by
  unfold readBase base
  rw [LiftRing.remainder_of _ (by rw [polynomial_degree d t ht hd]; omega)]
  simp

def decodeCount (ht : 0 < t) (x : O d t) : ℕ := (readBase d t ht x).val

theorem decodeCount_natCast (ht : 0 < t) (hd : d ≠ 0)
    (n : ℕ) (hn : n < 3 ^ t) : decodeCount d t ht (n : O d t) = n :=
  ActualLiftRing.decodeCount_natCast 3 d t ht hd n hn

theorem count_eq_zero_iff (ht : 0 < t) (hd : d ≠ 0)
    (n : ℕ) (hn : n < 3 ^ t) : (n : O d t) = 0 ↔ n = 0 :=
  ActualLiftRing.count_eq_zero_iff 3 d t ht hd n hn

theorem natCast_injective_below (ht : 0 < t) (hd : d ≠ 0)
    {a b : ℕ} (ha : a < 3 ^ t) (hb : b < 3 ^ t)
    (hab : (a : O d t) = (b : O d t)) : a = b :=
  ActualLiftRing.natCast_injective_below 3 d t ht hd ha hb hab


theorem two_isUnit (ht : 0 < t) : IsUnit (2 : O d t) := by
  apply isUnit_of_rho_ne_zero d t ht
  rw [map_ofNat]
  intro h
  have hz : (2 : ZMod 3) = 0 :=
    (algebraMap (ZMod 3) (E d)).injective (by simpa only [map_ofNat, map_zero] using h)
  exact (by decide : (2 : ZMod 3) ≠ 0) hz

end SubexponentialSAT.SqrtLog.RingCore

end

end OAI.Algorithms
