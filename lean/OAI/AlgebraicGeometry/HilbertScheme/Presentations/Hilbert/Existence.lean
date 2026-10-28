import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.RingTheory.Polynomial.HilbertPoly

/-! # Existence -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert

noncomputable section

/-!
Existence of Hilbert polynomials for the graded coordinate quotients.
For a monomial ideal, inclusion-exclusion counts the standard monomials
using the least common multiples of subsets of the generators. The
initial-ideal comparison extends this to every homogeneous ideal.
-/

open _root_.MvPolynomial
open scoped BigOperators

universe u

abbrev DegreeExponents (n d : ℕ) := {a : Fin (n + 1) →₀ ℕ // a.degree = d}

theorem card_degreeExponents (n d : ℕ) :
    Nat.card (DegreeExponents n d) = (d + n).choose n := by
  have e : Sym (Fin (n + 1)) d ≃ DegreeExponents n d := Sym.equivNatSum _ _
  rw [← Nat.card_congr e, Sym.natCard_sym_eq_choose, Nat.card_fin]
  have hnum : n + 1 + d - 1 = d + n := by omega
  rw [hnum]
  simpa only [Nat.add_sub_cancel_right] using Nat.choose_symm (Nat.le_add_left n d)

def degreeConeEquiv (n d : ℕ) (b : Fin (n + 1) →₀ ℕ) (hb : b.degree ≤ d) :
    {a : Fin (n + 1) →₀ ℕ // a.degree = d ∧ b ≤ a} ≃ DegreeExponents n (d - b.degree) where
  toFun a := ⟨a.val - b, by
    have h := congrArg Finsupp.degree (tsub_add_cancel_of_le a.property.2)
    rw [map_add, a.property.1] at h
    omega⟩
  invFun c := ⟨c.val + b, by
    rw [map_add, c.property]
    exact Nat.sub_add_cancel hb, le_add_self⟩
  left_inv a := Subtype.ext (tsub_add_cancel_of_le a.property.2)
  right_inv c := Subtype.ext (add_tsub_cancel_right c.val b)

theorem card_degreeCone (n d : ℕ) (b : Fin (n + 1) →₀ ℕ) (hb : b.degree ≤ d) :
    Nat.card {a : Fin (n + 1) →₀ ℕ // a.degree = d ∧ b ≤ a} =
      (d - b.degree + n).choose n := by
  rw [Nat.card_congr (degreeConeEquiv n d b hb), card_degreeExponents]

theorem card_degree_finset {n d : ℕ} (F : Finset (DegreeExponents n d))
    (p : (Fin (n + 1) →₀ ℕ) → Prop) (hF : ∀ a : DegreeExponents n d, a ∈ F ↔ p a.val) :
    F.card = Nat.card {a : Fin (n + 1) →₀ ℕ // a.degree = d ∧ p a} := by
  let e : F ≃ {a : Fin (n + 1) →₀ ℕ // a.degree = d ∧ p a} :=
    { toFun a := ⟨a.val.val, a.val.property, (hF a.val).mp a.property⟩
      invFun a := ⟨⟨a.val, a.property.1⟩, (hF _).mpr a.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Nat.card_congr e

def monomialHilbertPolynomial {n : ℕ} (G : Finset (Fin (n + 1) →₀ ℕ)) : Polynomial ℚ :=
  ∑ t ∈ G.powerset, (-1 : ℚ) ^ t.card • Polynomial.preHilbertPoly ℚ n (t.sup id).degree

theorem card_standard_eventually_polynomial {n : ℕ}
    (G : Finset (Fin (n + 1) →₀ ℕ)) (d : ℕ) (hd : (G.sup id).degree ≤ d) :
    (Nat.card {a : Fin (n + 1) →₀ ℕ // a.degree = d ∧ ∀ b ∈ G, ¬ b ≤ a} : ℚ) =
      (monomialHilbertPolynomial G).eval (d : ℚ) := by
  classical
  let : Fintype (DegreeExponents n d) := (Finsupp.finite_of_degree_eq (σ := Fin (n + 1)) d).fintype
  let C (b : Fin (n + 1) →₀ ℕ) : Finset (DegreeExponents n d) :=
    Finset.univ.filter (fun a => b ≤ a.val)
  have havoid : (G.inf (fun b => (C b)ᶜ)).card =
      Nat.card {a : Fin (n + 1) →₀ ℕ // a.degree = d ∧ ∀ b ∈ G, ¬ b ≤ a} := by
    apply card_degree_finset
    intro a
    simp [C, Finset.mem_inf]
  have hcone (t : Finset (Fin (n + 1) →₀ ℕ)) : (t.inf C).card =
      Nat.card {a : Fin (n + 1) →₀ ℕ // a.degree = d ∧ t.sup id ≤ a} := by
    apply card_degree_finset
    intro a
    simp [C, Finset.mem_inf, Finset.sup_le_iff]
  have hbound (t : Finset (Fin (n + 1) →₀ ℕ)) (ht : t ∈ G.powerset) :
      (t.sup id).degree ≤ d := by
    apply le_trans (Finsupp.degree_mono ?_) hd
    apply Finset.sup_le
    intro a ha
    exact Finset.le_sup (f := id) ((Finset.mem_powerset.mp ht) ha)
  have hie : (Nat.card {a : Fin (n + 1) →₀ ℕ //
      a.degree = d ∧ ∀ b ∈ G, ¬ b ≤ a} : ℚ) =
      ∑ t ∈ G.powerset, (-1 : ℚ) ^ t.card * ((t.inf C).card : ℚ) := by
    rw [← havoid]
    exact_mod_cast Finset.inclusion_exclusion_card_inf_compl G C
  rw [hie]
  simp only [monomialHilbertPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hcone, card_degreeCone n d (t.sup id) (hbound t ht),
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n ((hbound t ht).trans (Nat.le_add_right d n))]
  rw [Nat.sub_add_comm (hbound t ht)]

theorem monomialSpan_hasHilbertPolynomial {K : Type u} [Field K] {n : ℕ}
    (G : Finset (Fin (n + 1) →₀ ℕ)) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (MonomialBasis.GradedHilbert.monomialSpan K (G : Set (Fin (n + 1) →₀ ℕ))).toIdeal
      (monomialHilbertPolynomial G) := by
  refine ⟨(G.sup id).degree, fun d hd => ?_⟩
  rw [MonomialBasis.GradedHilbert.hilbertFunction_monomialSpan]
  exact card_standard_eventually_polynomial G d hd

/-- Every homogeneous coordinate ideal has a Hilbert polynomial, defined
using the actual dimensions of its graded quotients. -/
theorem exists_hilbertPolynomial {K : Type u} [Field K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) :
    ∃ P : Polynomial ℚ, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  obtain ⟨G, hG⟩ := (InitialIdeal.GradedHilbert.initialIdeal_isMonomial m I.toIdeal).finite_generators
  refine ⟨monomialHilbertPolynomial G, (InitialIdeal.GradedHilbert.hasHilbertPolynomial_initialIdeal_iff m I _).mp ?_⟩
  rw [hG]
  exact monomialSpan_hasHilbertPolynomial G

theorem existsUnique_hilbertPolynomial {K : Type u} [Field K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) :
    ∃! P : Polynomial ℚ, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  obtain ⟨P, hP⟩ := exists_hilbertPolynomial I
  exact ⟨P, hP, fun _ hQ => Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique hQ hP⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert
