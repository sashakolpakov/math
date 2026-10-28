import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Resultant Elimination -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ResultantElimination.Constructions.Elimination

noncomputable section

/-!
# Finite resultant tests for a common root

Encode a finite family by a polynomial in one auxiliary parameter. The
product of these encodings over the roots of a monic polynomial has bounded
degree. Testing its values at enough distinct constants detects whether a
root is common to the entire family.
-/

open _root_.Polynomial
open scoped BigOperators

def combination {m : ℕ} (Q : Fin m → Polynomial ℂ) (t : ℂ) : Polynomial ℂ :=
  ∑ j, (t ^ j.val) • Q j

def rootEncoding {m : ℕ} (Q : Fin m → Polynomial ℂ) (z : ℂ) : Polynomial ℂ :=
  ∑ j, monomial j.val ((Q j).eval z)

theorem rootEncoding_coeff {m : ℕ} (Q : Fin m → Polynomial ℂ) (z : ℂ) (j : Fin m) :
    (rootEncoding Q z).coeff j.val = (Q j).eval z := by
  simp [rootEncoding, finsetSum_coeff, coeff_monomial, Fin.val_inj]

theorem rootEncoding_natDegree_le {m : ℕ} (Q : Fin m → Polynomial ℂ) (z : ℂ) :
    (rootEncoding Q z).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_monomial_le _).trans j.isLt.le

theorem combination_natDegree_le {m d : ℕ} (Q : Fin m → Polynomial ℂ)
    (hQ : ∀ j, (Q j).natDegree ≤ d) (t : ℂ) : (combination Q t).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_smul_le _ _).trans (hQ j)

theorem eval_rootEncoding {m : ℕ} (Q : Fin m → Polynomial ℂ) (z t : ℂ) :
    (rootEncoding Q z).eval t = (combination Q t).eval z := by
  simp [rootEncoding, combination, eval_finsetSum, eval_smul, smul_eq_mul, mul_comm]

theorem rootEncoding_eq_zero_iff {m : ℕ} (Q : Fin m → Polynomial ℂ) (z : ℂ) :
    rootEncoding Q z = 0 ↔ ∀ j, (Q j).eval z = 0 := by
  constructor
  · intro h j
    rw [← rootEncoding_coeff Q z j, h, coeff_zero]
  · intro h
    simp [rootEncoding, h]

def rootEncodingProduct {m : ℕ} (P : Polynomial ℂ) (Q : Fin m → Polynomial ℂ) : Polynomial ℂ :=
  (P.roots.map (rootEncoding Q)).prod

theorem encodingProduct_natDegree_le {m : ℕ} (Q : Fin m → Polynomial ℂ) (s : Multiset ℂ) :
    (s.map (rootEncoding Q)).prod.natDegree ≤ s.card * m := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    exact natDegree_mul_le.trans (by
      calc
        _ ≤ m + s.card * m := add_le_add (rootEncoding_natDegree_le Q z) ih
        _ = _ := by ring)

theorem rootEncodingProduct_natDegree_le {m d : ℕ} (P : Polynomial ℂ)
    (Q : Fin m → Polynomial ℂ) (hP : P.natDegree = d) :
    (rootEncodingProduct P Q).natDegree ≤ d * m := by
  have h := encodingProduct_natDegree_le Q P.roots
  simpa only [rootEncodingProduct, (IsAlgClosed.splits P).natDegree_eq_card_roots.symm, hP] using h

theorem eval_encodingProduct_eq_resultant {m d : ℕ} (P : Polynomial ℂ)
    (hP : P.Monic) (hdeg : P.natDegree = d) (Q : Fin m → Polynomial ℂ)
    (hQ : ∀ j, (Q j).natDegree ≤ d) (t : ℂ) :
    (rootEncodingProduct P Q).eval t = P.resultant (combination Q t) d d := by
  have hr := P.resultant_eq_prod_eval (combination Q t) d
    (combination_natDegree_le Q hQ t) (IsAlgClosed.splits P)
  rw [hdeg, hP.leadingCoeff, one_pow, one_mul] at hr
  rw [hr]
  simp only [rootEncodingProduct, eval_multiset_prod, Multiset.map_map, Function.comp_def,
    eval_rootEncoding]

theorem encodingProduct_eq_zero_iff {m : ℕ} (P : Polynomial ℂ) (hP : P ≠ 0)
    (Q : Fin m → Polynomial ℂ) :
    rootEncodingProduct P Q = 0 ↔ ∃ z, P.eval z = 0 ∧ ∀ j, (Q j).eval z = 0 := by
  rw [rootEncodingProduct, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨z, hz, henc⟩
    exact ⟨z, (mem_roots hP).mp hz, (rootEncoding_eq_zero_iff Q z).mp henc⟩
  · rintro ⟨z, hz, hQ⟩
    exact ⟨z, (mem_roots hP).mpr hz, (rootEncoding_eq_zero_iff Q z).mpr hQ⟩

/-- A common root is detected by `d*m+1` fixed resultant evaluations. -/
theorem common_root_iff_resultant_tests {m d : ℕ} (P : Polynomial ℂ)
    (hP : P.Monic) (hdeg : P.natDegree = d) (Q : Fin m → Polynomial ℂ)
    (hQ : ∀ j, (Q j).natDegree ≤ d) :
    (∃ z, P.eval z = 0 ∧ ∀ j, (Q j).eval z = 0) ↔
      ∀ k : Fin (d * m + 1), P.resultant (combination Q (k.val : ℂ)) d d = 0 := by
  rw [← encodingProduct_eq_zero_iff P hP.ne_zero Q]
  constructor
  · intro h k
    rw [← eval_encodingProduct_eq_resultant P hP hdeg Q hQ, h, eval_zero]
  · intro h
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (rootEncodingProduct P Q)
      (f := fun k : Fin (d * m + 1) => (k.val : ℂ))
    · intro i j hij
      exact Fin.ext (Nat.cast_injective hij)
    · intro k
      rw [eval_encodingProduct_eq_resultant P hP hdeg Q hQ]
      exact h k
    · simpa only [Fintype.card_fin] using
        lt_of_le_of_lt (rootEncodingProduct_natDegree_le P Q hdeg) (Nat.lt_succ_self _)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ResultantElimination.Constructions.Elimination
