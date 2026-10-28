import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

structure Data (d : ℕ) where
  coefficients : Fin d → ZMod 3
  irreducible : Irreducible (QuarticSearch.poly coefficients)

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

abbrev Base (t : ℕ) := LiftRing.Base 3 t

def residuePolynomial : (ZMod 3)[X] := QuarticSearch.poly a.coefficients

def F : (Base t)[X] :=
  QuarticSearch.poly (fun i => ((a.coefficients i).val : Base t))

theorem residuePolynomial_monic : a.residuePolynomial.Monic := QuarticSearch.poly_monic _
theorem residuePolynomial_irreducible : Irreducible a.residuePolynomial := a.irreducible
@[simp] theorem residuePolynomial_degree : a.residuePolynomial.natDegree = d :=
  QuarticSearch.poly_natDegree _

abbrev E := LiftRing.Extension a.residuePolynomial
abbrev O := LiftRing.Extension (a.F t)

instance fieldE : Field a.E := LiftRing.extensionField a.residuePolynomial_irreducible
instance fieldFinite : Finite a.E := LiftRing.extension_finite_type a.residuePolynomial_monic
instance fieldFintype : Fintype a.E := Fintype.ofFinite _

theorem F_monic (_ht : 0 < t) : (a.F t).Monic := by
  let _ : Fact (1 < 3 ^ t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt _ht) (by decide)⟩
  exact QuarticSearch.poly_monic _

@[simp] theorem F_degree (ht : 0 < t) : (a.F t).natDegree = d := by
  let _ : Fact (1 < 3 ^ t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  exact QuarticSearch.poly_natDegree _

theorem F_map (ht : 0 < t) :
    (a.F t).map (LiftRing.baseReduction 3 t ht) = a.residuePolynomial := by
  rw [F, QuarticSearch.map_poly]
  apply congrArg QuarticSearch.poly
  funext i
  simp only [map_natCast, ZMod.natCast_zmod_val]

def reducedEquiv (ht : 0 < t) :
    LiftRing.Extension ((a.F t).map (LiftRing.baseReduction 3 t ht)) ≃+* a.E :=
  Ideal.quotEquivOfEq
    (congrArg (fun f : (ZMod 3)[X] => Ideal.span ({f} : Set (ZMod 3)[X])) (a.F_map t ht))

def rho (ht : 0 < t) : a.O t →+* a.E :=
  (a.reducedEquiv t ht).toRingHom.comp (LiftRing.residue 3 t ht (a.F t))

@[simp] theorem rho_mk (ht : 0 < t) (q : (Base t)[X]) :
    a.rho t ht (LiftRing.mk (a.F t) q) =
      LiftRing.mk a.residuePolynomial (q.map (LiftRing.baseReduction 3 t ht)) := rfl

theorem rho_surjective (ht : 0 < t) : Function.Surjective (a.rho t ht) :=
  (a.reducedEquiv t ht).surjective.comp (LiftRing.residue_surjective 3 t ht (a.F t))

theorem rho_eq_zero_iff (ht : 0 < t) (x : a.O t) :
    a.rho t ht x = 0 ↔ (3 : a.O t) ∣ x := by
  change a.reducedEquiv t ht (LiftRing.residue 3 t ht (a.F t) x) = 0 ↔ _
  rw [← (a.reducedEquiv t ht).map_zero, (a.reducedEquiv t ht).injective.eq_iff]
  exact LiftRing.residue_eq_zero_iff 3 t ht (a.F_monic t ht) x

theorem rho_ker (ht : 0 < t) :
    RingHom.ker (a.rho t ht) = Ideal.span ({(3 : a.O t)} : Set (a.O t)) := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_span_singleton, a.rho_eq_zero_iff t ht]

theorem prime_power_zero : (3 : a.O t) ^ t = 0 := LiftRing.prime_power_zero 3 t (a.F t)

theorem pow_eq_zero_of_rho_eq_zero (ht : 0 < t) {x : a.O t}
    (hx : a.rho t ht x = 0) : x ^ t = 0 := by
  obtain ⟨b, rfl⟩ := (a.rho_eq_zero_iff t ht x).mp hx
  rw [mul_pow, a.prime_power_zero, zero_mul]

theorem isUnit_of_rho_ne_zero (ht : 0 < t) {x : a.O t}
    (hx : a.rho t ht x ≠ 0) : IsUnit x :=
  NilpotentDefect.isUnit_of_residue_ne_zero
    (a.rho t ht) (a.rho_surjective t ht) (3 : a.O t) t
    (a.prime_power_zero t) (fun z hz => (a.rho_eq_zero_iff t ht z).mp hz) hx

theorem isUnit_iff_rho_ne_zero (ht : 0 < t) (x : a.O t) :
    IsUnit x ↔ a.rho t ht x ≠ 0 := by
  constructor
  · intro hx
    exact (hx.map (a.rho t ht)).ne_zero
  · exact a.isUnit_of_rho_ne_zero t ht

def fieldCoordinates : a.E ≃ₗ[ZMod 3] (Fin d → ZMod 3) :=
  SubexpActualRing.coordinatesOfDegree a.residuePolynomial a.residuePolynomial_monic
    a.residuePolynomial_degree

@[simp] theorem fieldCoordinates_symm_apply (c : Fin d → ZMod 3) :
    a.fieldCoordinates.symm c =
      LiftRing.mk a.residuePolynomial (∑ i : Fin d, monomial i (c i)) :=
  SubexpActualRing.coordinatesOfDegree_symm_apply _ _ _ c

def coordinates (ht : 0 < t) : a.O t ≃ₗ[Base t] (Fin d → Base t) :=
  SubexpActualRing.coordinatesOfDegree (a.F t) (a.F_monic t ht) (a.F_degree t ht)

@[simp] theorem coordinates_apply (ht : 0 < t) (x : a.O t) (i : Fin d) :
    a.coordinates t ht x i = (LiftRing.remainder (a.F_monic t ht) x).coeff i :=
  SubexpActualRing.coordinatesOfDegree_apply _ _ _ x i

@[simp] theorem coordinates_symm_apply (ht : 0 < t) (c : Fin d → Base t) :
    (a.coordinates t ht).symm c = LiftRing.mk (a.F t) (∑ i : Fin d, monomial i (c i)) :=
  SubexpActualRing.coordinatesOfDegree_symm_apply _ _ _ c

/-- No preimage choice is used: lift every residue coefficient separately. -/
def sectionValue (ht : 0 < t) (z : a.E) : a.O t :=
  (a.coordinates t ht).symm (fun i => ((a.fieldCoordinates z i).val : Base t))

@[simp] theorem rho_sectionValue (ht : 0 < t) (z : a.E) :
    a.rho t ht (a.sectionValue t ht z) = z := by
  rw [sectionValue, coordinates_symm_apply, rho_mk]
  simp only [Polynomial.map_sum, Polynomial.map_monomial, map_natCast, ZMod.natCast_zmod_val]
  rw [← fieldCoordinates_symm_apply]
  exact a.fieldCoordinates.symm_apply_apply z

def base : Base t →+* a.O t := LiftRing.of (a.F t)

theorem base_injective (ht : 0 < t) (hd : d ≠ 0) : Function.Injective (a.base t) :=
  LiftRing.base_injective (a.F_monic t ht) (by rw [a.F_degree t ht]; omega)

def readBase (ht : 0 < t) (x : a.O t) : Base t :=
  (LiftRing.remainder (a.F_monic t ht) x).coeff 0

@[simp] theorem readBase_base (ht : 0 < t) (hd : d ≠ 0) (c : Base t) :
    a.readBase t ht (a.base t c) = c := by
  unfold readBase base
  rw [LiftRing.remainder_of _ (by rw [a.F_degree t ht]; omega)]
  simp

def decodeCount (ht : 0 < t) (x : a.O t) : ℕ := (a.readBase t ht x).val

theorem decodeCount_natCast (ht : 0 < t) (hd : d ≠ 0) (n : ℕ) (hn : n < 3 ^ t) :
    a.decodeCount t ht (n : a.O t) = n :=
  LiftRing.decodeCount_natCast 3 t (a.F_monic t ht) (by rw [a.F_degree t ht]; omega) n hn

theorem count_eq_zero_iff (ht : 0 < t) (hd : d ≠ 0) (n : ℕ) (hn : n < 3 ^ t) :
    (n : a.O t) = 0 ↔ n = 0 :=
  LiftRing.count_eq_zero_iff 3 t (a.F_monic t ht) (by rw [a.F_degree t ht]; omega) n hn

theorem finite_type (ht : 0 < t) : Finite (a.O t) :=
  LiftRing.extension_finite_type (a.F_monic t ht)

theorem cardinality (ht : 0 < t) : Nat.card (a.O t) = (3 ^ t) ^ d := by
  simpa only [a.F_degree t ht] using LiftRing.natCard_lambda 3 t (a.F_monic t ht)

theorem residue_cardinality : Nat.card a.E = 3 ^ d := by
  simpa only [a.residuePolynomial_degree, Nat.card_zmod] using
    LiftRing.natCard_extension a.residuePolynomial_monic

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
