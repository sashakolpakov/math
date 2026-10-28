import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuarticSearch
import OAI.Algorithms.SubexponentialSAT.LiftRing
import OAI.Algorithms.SubexponentialSAT.TableInterpolation
import OAI.Algorithms.SubexponentialSAT.CosetInvariance
import OAI.Algorithms.SubexponentialSAT.NilpotentDefect

namespace OAI.Algorithms

/-!
# The counting ring from the executable quartic search

Both the residue field and the prime-power ring use the coefficients returned
by QuarticSearch. No separately chosen minimum polynomial enters this file.
The polynomial quotient is the semantic interpretation of those coefficients;
the executable four-coordinate arithmetic is implemented separately.
-/

noncomputable section
namespace SubexponentialSAT.SubexpActualRing

open Polynomial

/-- Reindex the linear remainder coordinates by a proved exact degree. -/
def coordinatesOfDegree {A : Type*} [CommRing A] {d : ℕ}
    (f : A[X]) (hf : f.Monic) (hd : f.natDegree = d) :
    LiftRing.Extension f ≃ₗ[A] (Fin d → A) :=
  hd ▸ LiftRing.coordinates hf

@[simp] theorem coordinatesOfDegree_apply {A : Type*} [CommRing A] {d : ℕ}
    (f : A[X]) (hf : f.Monic) (hd : f.natDegree = d)
    (x : LiftRing.Extension f) (i : Fin d) :
    coordinatesOfDegree f hf hd x i = (LiftRing.remainder hf x).coeff i := by
  subst d
  rfl

@[simp] theorem coordinatesOfDegree_symm_apply {A : Type*} [CommRing A] {d : ℕ}
    (f : A[X]) (hf : f.Monic) (hd : f.natDegree = d) (a : Fin d → A) :
    (coordinatesOfDegree f hf hd).symm a =
      LiftRing.mk f (∑ i : Fin d, monomial i (a i)) := by
  subst d
  rfl

variable (p μ : ℕ) [Fact p.Prime]

/-- The polynomial selected by the executable exhaustive quartic search. -/
def residuePolynomial : (ZMod p)[X] :=
  QuarticSearch.poly (QuarticSearch.coefficients p)

/-- Coefficientwise integer-representative lift of that exact polynomial. -/
def F : (LiftRing.Base p μ)[X] :=
  QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ)

theorem residuePolynomial_monic : (residuePolynomial p).Monic :=
  QuarticSearch.coefficients_monic p

theorem residuePolynomial_irreducible : Irreducible (residuePolynomial p) :=
  QuarticSearch.coefficients_irreducible p

@[simp] theorem residuePolynomial_degree : (residuePolynomial p).natDegree = 4 :=
  QuarticSearch.coefficients_natDegree p

/-- The actual residue field, defined by the selected polynomial. -/
abbrev E := LiftRing.Extension (residuePolynomial p)

instance fieldE : Field (E p) :=
  LiftRing.extensionField (residuePolynomial_irreducible p)

instance finiteE : Finite (E p) :=
  LiftRing.extension_finite_type (residuePolynomial_monic p)

instance fieldFintype : Fintype (E p) := Fintype.ofFinite _

instance fieldFiniteDimensional : Module.Finite (ZMod p) (E p) :=
  LiftRing.extension_finite (residuePolynomial_monic p)

/-- The actual prime-power ring, definitionally the quotient used by the
four-coordinate arithmetic refinement. -/
abbrev Ring := LiftRing.Extension (F p μ)

theorem modulus_gt_one (hμ : 0 < μ) : 1 < p ^ μ :=
  Nat.one_lt_pow (Nat.ne_of_gt hμ) (Fact.out : p.Prime).one_lt

omit [Fact (Nat.Prime p)] in
theorem F_monic (_hμ : 0 < μ) : (F p μ).Monic :=
  QuarticSearch.poly_monic _

@[simp] theorem F_degree (hμ : 0 < μ) : (F p μ).natDegree = 4 := by
  let _ : Fact (1 < p ^ μ) := ⟨modulus_gt_one p μ hμ⟩
  exact QuarticSearch.poly_natDegree _

/-- Reduction yields the same selected residue polynomial. -/
theorem F_map (hμ : 0 < μ) :
    (F p μ).map (LiftRing.baseReduction p μ hμ) = residuePolynomial p := by
  rw [F, QuarticSearch.map_poly]
  apply congrArg QuarticSearch.poly
  funext i
  simp only [QuarticSearch.liftedCoefficients, map_natCast, ZMod.natCast_zmod_val]

/-- Transport along polynomial equality, with no choice of a new field. -/
def reducedEquiv (hμ : 0 < μ) :
    LiftRing.Extension ((F p μ).map (LiftRing.baseReduction p μ hμ)) ≃+* E p :=
  Ideal.quotEquivOfEq
    (congrArg (fun f : (ZMod p)[X] => Ideal.span ({f} : Set (ZMod p)[X]))
      (F_map p μ hμ))

/-- The exact residue map used by the counting argument. -/
def rho (hμ : 0 < μ) : Ring p μ →+* E p :=
  (reducedEquiv p μ hμ).toRingHom.comp (LiftRing.residue p μ hμ (F p μ))

@[simp] theorem rho_mk (hμ : 0 < μ) (q : (LiftRing.Base p μ)[X]) :
    rho p μ hμ (LiftRing.mk (F p μ) q) =
      LiftRing.mk (residuePolynomial p) (q.map (LiftRing.baseReduction p μ hμ)) := rfl

theorem rho_surjective (hμ : 0 < μ) : Function.Surjective (rho p μ hμ) :=
  (reducedEquiv p μ hμ).surjective.comp
    (LiftRing.residue_surjective p μ hμ (F p μ))

theorem rho_eq_zero_iff (hμ : 0 < μ) (x : Ring p μ) :
    rho p μ hμ x = 0 ↔ (p : Ring p μ) ∣ x := by
  change reducedEquiv p μ hμ (LiftRing.residue p μ hμ (F p μ) x) = 0 ↔ _
  rw [← (reducedEquiv p μ hμ).map_zero, (reducedEquiv p μ hμ).injective.eq_iff]
  exact LiftRing.residue_eq_zero_iff p μ hμ (F_monic p μ hμ) x

theorem rho_ker (hμ : 0 < μ) :
    RingHom.ker (rho p μ hμ) = Ideal.span ({(p : Ring p μ)} : Set (Ring p μ)) := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_span_singleton, rho_eq_zero_iff p μ hμ]

omit [Fact p.Prime] in
theorem prime_power_zero : (p : Ring p μ) ^ μ = 0 :=
  LiftRing.prime_power_zero p μ (F p μ)

theorem isUnit_of_rho_ne_zero (hμ : 0 < μ) {x : Ring p μ}
    (hx : rho p μ hμ x ≠ 0) : IsUnit x :=
  NilpotentDefect.isUnit_of_residue_ne_zero
    (rho p μ hμ) (rho_surjective p μ hμ) (p : Ring p μ) μ
    (prime_power_zero p μ) (fun z hz => (rho_eq_zero_iff p μ hμ z).mp hz) hx

/-- The standard integer representatives of prime-field coordinates. -/
def coordinateLift (z : ZMod p) : Ring p μ := (z.val : Ring p μ)

theorem rho_coordinateLift (hμ : 0 < μ) (z : ZMod p) :
    rho p μ hμ (coordinateLift p μ z) = algebraMap (ZMod p) (E p) z := by
  change rho p μ hμ (z.val : Ring p μ) = _
  rw [map_natCast]
  simpa only [map_natCast] using
    congrArg (algebraMap (ZMod p) (E p)) (ZMod.natCast_zmod_val z)

theorem coordinateLift_unitDifferences :
    TableInterpolation.UnitDifferences (coordinateLift p μ) := by
  intro a b hab
  apply TableInterpolation.unitDifferences_lambda_integerLabels p μ
    (Fact.out : p.Prime) (F p μ)
      (⟨a.val, a.val_lt⟩ : Fin p) (⟨b.val, b.val_lt⟩ : Fin p)
  intro heq
  apply hab
  have hv := congrArg Fin.val heq
  simpa using congrArg (fun n : ℕ => (n : ZMod p)) hv

/-- Four residue-field coordinates in the power basis. -/
def fieldCoordinates : E p ≃ₗ[ZMod p] (Fin 4 → ZMod p) :=
  coordinatesOfDegree (residuePolynomial p) (residuePolynomial_monic p)
    (residuePolynomial_degree p)

@[simp] theorem fieldCoordinates_apply (x : E p) (i : Fin 4) :
    fieldCoordinates p x i =
      (LiftRing.remainder (residuePolynomial_monic p) x).coeff i :=
  coordinatesOfDegree_apply _ _ _ x i

@[simp] theorem fieldCoordinates_symm_apply (a : Fin 4 → ZMod p) :
    (fieldCoordinates p).symm a =
      LiftRing.mk (residuePolynomial p) (∑ i : Fin 4, monomial i (a i)) :=
  coordinatesOfDegree_symm_apply _ _ _ a

theorem fieldCoordinates_algebraMap (a : ZMod p) (i : Fin 4) :
    fieldCoordinates p (algebraMap (ZMod p) (E p) a) i = (C a).coeff i := by
  rw [fieldCoordinates_apply]
  change (LiftRing.remainder (residuePolynomial_monic p)
    (LiftRing.of (residuePolynomial p) a)).coeff i = _
  rw [LiftRing.remainder_of _ (by rw [residuePolynomial_degree]; decide)]

theorem extension_finrank : Module.finrank (ZMod p) (E p) = 4 := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    (fieldCoordinates p).finrank_eq

theorem extension_natCard : Nat.card (E p) = p ^ 4 := by
  simpa only [residuePolynomial_degree, Nat.card_zmod] using
    LiftRing.natCard_extension (residuePolynomial_monic p)

theorem extension_card : Fintype.card (E p) = p ^ 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact extension_natCard p

/-- A semantic enumeration of all nonzero field elements. Its implementation
on explicit coefficient words is a separate refinement obligation. -/
def nodeEquiv : Fin (p ^ 4 - 1) ≃ {z : E p // z ≠ 0} := by
  classical
  apply (Fintype.equivFinOfCardEq _).symm
  rw [Fintype.card_subtype_compl]
  simp [extension_card p]

/-- The semantic ring is precisely a free module of four base-ring
coefficients; the coefficient-selection algorithm determines its modulus. -/
def ringCoordinates (hμ : 0 < μ) :
    Ring p μ ≃ₗ[LiftRing.Base p μ] (Fin 4 → LiftRing.Base p μ) :=
  coordinatesOfDegree (F p μ) (F_monic p μ hμ) (F_degree p μ hμ)

@[simp] theorem ringCoordinates_apply (hμ : 0 < μ) (x : Ring p μ) (i : Fin 4) :
    ringCoordinates p μ hμ x i = (LiftRing.remainder (F_monic p μ hμ) x).coeff i :=
  coordinatesOfDegree_apply _ _ _ x i

@[simp] theorem ringCoordinates_symm_apply (hμ : 0 < μ)
    (a : Fin 4 → LiftRing.Base p μ) :
    (ringCoordinates p μ hμ).symm a =
      LiftRing.mk (F p μ) (∑ i : Fin 4, monomial i (a i)) :=
  coordinatesOfDegree_symm_apply _ _ _ a

theorem ringCoordinates_of (hμ : 0 < μ) (a : LiftRing.Base p μ) (i : Fin 4) :
    ringCoordinates p μ hμ (LiftRing.of (F p μ) a) i = (C a).coeff i := by
  rw [ringCoordinates_apply,
    LiftRing.remainder_of _ (by rw [F_degree p μ hμ]; decide)]

/-- The explicit residue section lifts the four standard coefficient
representatives individually. It uses no choice of preimages. -/
def sectionValue (hμ : 0 < μ) (z : E p) : Ring p μ :=
  (ringCoordinates p μ hμ).symm
    (fun i => ((fieldCoordinates p z i).val : LiftRing.Base p μ))

@[simp] theorem rho_sectionValue (hμ : 0 < μ) (z : E p) :
    rho p μ hμ (sectionValue p μ hμ z) = z := by
  rw [sectionValue, ringCoordinates_symm_apply, rho_mk]
  simp only [Polynomial.map_sum, Polynomial.map_monomial,
    map_natCast, ZMod.natCast_zmod_val]
  rw [← fieldCoordinates_symm_apply]
  exact (fieldCoordinates p).symm_apply_apply z

/-- On prime-field constants the section is exactly the original integer lift. -/
theorem sectionValue_algebraMap (hμ : 0 < μ) (a : ZMod p) :
    sectionValue p μ hμ (algebraMap (ZMod p) (E p) a) = coordinateLift p μ a := by
  apply (ringCoordinates p μ hμ).injective
  funext i
  simp only [sectionValue, LinearEquiv.apply_symm_apply]
  rw [fieldCoordinates_algebraMap]
  have hc : coordinateLift p μ a = LiftRing.of (F p μ) (a.val : LiftRing.Base p μ) := by
    simp only [coordinateLift, map_natCast]
  rw [hc, ringCoordinates_of]
  by_cases hi : (i : ℕ) = 0 <;> simp [Polynomial.coeff_C, hi]

@[simp] theorem sectionValue_zero (hμ : 0 < μ) :
    sectionValue p μ hμ 0 = 0 := by
  simpa [coordinateLift] using sectionValue_algebraMap p μ hμ (0 : ZMod p)

@[simp] theorem sectionValue_one (hμ : 0 < μ) :
    sectionValue p μ hμ 1 = 1 := by
  let _ : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  simpa only [map_one, coordinateLift, ZMod.val_one, Nat.cast_one] using
    sectionValue_algebraMap p μ hμ (1 : ZMod p)

/-- Package the explicit four-coefficient section for the beta interface. -/
def residueSection (hμ : 0 < μ) : CosetInvariance.ResidueSection (rho p μ hμ) where
  lift := sectionValue p μ hμ
  residue_lift := rho_sectionValue p μ hμ

omit [Fact (Nat.Prime p)] in
theorem ring_free (hμ : 0 < μ) : Module.Free (LiftRing.Base p μ) (Ring p μ) :=
  LiftRing.extension_free (F_monic p μ hμ)

omit [Fact (Nat.Prime p)] in
theorem ring_finite_module (hμ : 0 < μ) :
    Module.Finite (LiftRing.Base p μ) (Ring p μ) :=
  LiftRing.extension_finite (F_monic p μ hμ)

theorem ring_finite_type (hμ : 0 < μ) : Finite (Ring p μ) :=
  LiftRing.extension_finite_type (F_monic p μ hμ)

theorem ring_natCard (hμ : 0 < μ) : Nat.card (Ring p μ) = (p ^ μ) ^ 4 := by
  simpa only [F_degree p μ hμ] using LiftRing.natCard_lambda p μ (F_monic p μ hμ)

theorem base_injective (hμ : 0 < μ) : Function.Injective (LiftRing.of (F p μ)) :=
  LiftRing.base_injective (F_monic p μ hμ) (by rw [F_degree p μ hμ]; decide)

/-- Decode the constant coefficient of the canonical remainder. -/
def decodeCount (hμ : 0 < μ) (x : Ring p μ) : ℕ :=
  LiftRing.decodeCount p μ (F_monic p μ hμ) x

/-- Decoding reads precisely the first field of the four-coordinate representation. -/
theorem decodeCount_eq_coordinate (hμ : 0 < μ) (x : Ring p μ) :
    decodeCount p μ hμ x = (ringCoordinates p μ hμ x 0).val := by
  rw [ringCoordinates_apply]
  rfl

theorem decodeCount_natCast (hμ : 0 < μ) (n : ℕ) (hn : n < p ^ μ) :
    decodeCount p μ hμ (n : Ring p μ) = n :=
  LiftRing.decodeCount_natCast p μ (F_monic p μ hμ)
    (by rw [F_degree p μ hμ]; decide) n hn

theorem count_eq_zero_iff (hμ : 0 < μ) (n : ℕ) (hn : n < p ^ μ) :
    (n : Ring p μ) = 0 ↔ n = 0 :=
  LiftRing.count_eq_zero_iff p μ (F_monic p μ hμ)
    (by rw [F_degree p μ hμ]; decide) n hn

theorem natCast_injective_below (hμ : 0 < μ)
    {a b : ℕ} (ha : a < p ^ μ) (hb : b < p ^ μ)
    (hab : (a : Ring p μ) = (b : Ring p μ)) : a = b := by
  calc
    a = decodeCount p μ hμ (a : Ring p μ) := (decodeCount_natCast p μ hμ a ha).symm
    _ = decodeCount p μ hμ (b : Ring p μ) := congrArg (decodeCount p μ hμ) hab
    _ = b := decodeCount_natCast p μ hμ b hb

end SubexponentialSAT.SubexpActualRing

end

end OAI.Algorithms
