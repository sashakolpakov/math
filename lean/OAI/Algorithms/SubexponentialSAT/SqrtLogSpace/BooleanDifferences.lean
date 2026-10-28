import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

/-! Boolean finite differences (ETH, Lemma `boolean-differences`).
The finite sets in this module specify sums; they are not operational enumerators. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences

open scoped BigOperators

/-- The original support counting envelope. -/
def supportFamily (n J : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun E => E.card < J)

/-- Valid correction pairs form a subset of the square of the support envelope. -/
def pairFamily (n J : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (supportFamily n J ×ˢ supportFamily n J).filter (fun p => p.2 ⊆ p.1)

@[simp] theorem mem_supportFamily {n J : ℕ} {E : Finset (Fin n)} :
    E ∈ supportFamily n J ↔ E.card < J := by
  simp [supportFamily]

@[simp] theorem mem_pairFamily {n J : ℕ} {E U : Finset (Fin n)} :
    (E, U) ∈ pairFamily n J ↔ E.card < J ∧ U ⊆ E := by
  simp only [pairFamily, Finset.mem_filter, Finset.mem_product, mem_supportFamily]
  exact ⟨fun h => ⟨h.1.1, h.2⟩,
    fun h => ⟨⟨h.1, (Finset.card_le_card h.2).trans_lt h.1⟩, h.2⟩⟩

theorem pairFamily_card_le (n J : ℕ) :
    (pairFamily n J).card ≤ (supportFamily n J).card ^ 2 := by
  calc
    _ ≤ (supportFamily n J ×ˢ supportFamily n J).card := Finset.card_filter_le _ _
    _ = _ := by simp [pow_two]

theorem pairFamily_eq_biUnion (n J : ℕ) :
    pairFamily n J = (supportFamily n J).biUnion
      (fun E => E.powerset.image (fun U => (E, U))) := by
  ext p
  rcases p with ⟨E, U⟩
  simp [Finset.mem_biUnion, Finset.mem_image]

/-- Coordinate transport preserves the exact support counting envelope. -/
theorem supportFamily_map_equiv {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (e : Fin n ≃ V) (J : ℕ) :
    (supportFamily n J).map e.finsetCongr.toEmbedding =
      Finset.univ.filter (fun E : Finset V => E.card < J) := by
  ext E
  simp [Finset.mem_map_equiv, Equiv.finsetCongr]

/-- A coordinate equivalence transports the iterator's pairs exactly. This is
an internal indexing change, not a change of the ambient assignment universe. -/
theorem pairFamily_map_equiv {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (e : Fin n ≃ V) (J : ℕ) :
    (pairFamily n J).map (Equiv.prodCongr e.finsetCongr e.finsetCongr).toEmbedding =
      Finset.univ.filter (fun p : Finset V × Finset V => p.1.card < J ∧ p.2 ⊆ p.1) := by
  ext p
  rcases p with ⟨E, U⟩
  simp [Finset.mem_map_equiv, Equiv.prodCongr, Equiv.finsetCongr]

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- Substitution of the Boolean characteristic vector of a set. -/
def evalAt (U : Finset V) : MvPolynomial V R →+* R :=
  MvPolynomial.eval (fun v => if v ∈ U then 1 else 0)

/-- The coefficient of the Boolean multilinearization indexed by `E`. -/
def difference (E : Finset V) (p : MvPolynomial V R) : R :=
  ∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) * evalAt U p

private theorem subset_sign_sum (E T : Finset V) :
    (∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
      (if T ⊆ U then 1 else 0)) = if T = E then 1 else 0 := by
  induction E using Finset.induction_on generalizing T with
  | empty => simp only [Finset.powerset_empty, Finset.sum_singleton,
      Finset.card_empty, Nat.sub_self, pow_zero, one_mul, Finset.subset_empty]
  | @insert a E ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have hcard (U : Finset V) (hU : U ∈ E.powerset) : U.card ≤ E.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hU)
    have hnot (U : Finset V) (hU : U ∈ E.powerset) : a ∉ U :=
      fun h => ha (Finset.mem_powerset.mp hU h)
    by_cases hat : a ∈ T
    · have hzero : (∑ U ∈ E.powerset, (-1 : R) ^ ((insert a E).card - U.card) *
          (if T ⊆ U then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro U hU
        simp [show ¬T ⊆ U from fun h => hnot U hU (h hat)]
      rw [hzero, zero_add]
      calc
        _ = ∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
            (if T.erase a ⊆ U then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro U hU
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem (hnot U hU)]
          have hsub : T ⊆ insert a U ↔ T.erase a ⊆ U := by
            constructor
            · intro h v hv
              exact (Finset.mem_insert.mp (h (Finset.mem_erase.mp hv).2)).resolve_left
                (Finset.mem_erase.mp hv).1
            · intro h v hv
              by_cases hav : v = a
              · simp [hav]
              · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.mpr ⟨hav, hv⟩))
          simp [hsub]
        _ = if T.erase a = E then 1 else 0 := ih _
        _ = _ := by
          have heq : T.erase a = E ↔ T = insert a E := by
            constructor
            · intro h; rw [← h, Finset.insert_erase hat]
            · intro h; subst T; simp [ha]
          simp only [heq]
    · have hsub (U : Finset V) : T ⊆ insert a U ↔ T ⊆ U := by
        constructor
        · intro h v hv
          exact (Finset.mem_insert.mp (h hv)).resolve_left (fun h => hat (h ▸ hv))
        · exact fun h => h.trans (Finset.subset_insert _ _)
      have hfirst : (∑ U ∈ E.powerset, (-1 : R) ^ ((insert a E).card - U.card) *
          (if T ⊆ U then 1 else 0)) =
          -(∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
            (if T ⊆ U then 1 else 0)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro U hU
        rw [Finset.card_insert_of_notMem ha,
          show E.card + 1 - U.card = E.card - U.card + 1 by
            have := hcard U hU
            omega, pow_succ]
        split_ifs <;> simp
      rw [hfirst]
      have hsecond : (∑ U ∈ E.powerset,
          (-1 : R) ^ ((insert a E).card - (insert a U).card) *
            (if T ⊆ insert a U then 1 else 0)) =
          ∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
            (if T ⊆ U then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro U hU
        simp [Finset.card_insert_of_notMem ha,
          Finset.card_insert_of_notMem (hnot U hU), hsub]
      rw [hsecond, neg_add_cancel]
      simp [show T ≠ insert a E from fun h => hat (h.symm ▸ Finset.mem_insert_self a E)]

@[simp] theorem evalAt_monomial (U : Finset V) (d : V →₀ ℕ) (c : R) :
    evalAt U (MvPolynomial.monomial d c) = if d.support ⊆ U then c else 0 := by
  classical
  rw [evalAt, MvPolynomial.eval_monomial, Finsupp.prod]
  by_cases h : d.support ⊆ U
  · rw [ite_eq_left h, Finset.prod_eq_one (fun v hv => by simp [h hv]), mul_one]
  · obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp h
    have hd : d v ≠ 0 := Finsupp.mem_support_iff.mp hv
    rw [Finset.prod_eq_zero hv (by simp [hvU, hd]), mul_zero, ite_eq_right h]

theorem difference_monomial (E : Finset V) (d : V →₀ ℕ) (c : R) :
    difference E (MvPolynomial.monomial d c) = if d.support = E then c else 0 := by
  classical
  simp only [difference, evalAt_monomial]
  calc
    _ = (∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
          (if d.support ⊆ U then 1 else 0)) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      split_ifs <;> simp
    _ = _ := by rw [subset_sign_sum]; split_ifs <;> simp

theorem difference_eq_sum_coeff (E : Finset V) (p : MvPolynomial V R) :
    difference E p = ∑ d ∈ p.support,
      if d.support = E then p.coeff d else 0 := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp only [difference, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact difference_monomial E d (p.coeff d)

omit [DecidableEq V] in
/-- Degree controls the number of distinct variables in every monomial. -/
theorem support_card_le_totalDegree (p : MvPolynomial V R) {d : V →₀ ℕ}
    (hd : d ∈ p.support) : d.support.card ≤ p.totalDegree := by
  calc
    d.support.card = ∑ v ∈ d.support, 1 := by simp
    _ ≤ ∑ v ∈ d.support, d v := Finset.sum_le_sum (fun v hv =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

/-- Recovery at one Boolean point; high-degree supports do not contribute. -/
theorem evalAt_eq_sum_differences [Fintype V] {J : ℕ} (X : Finset V)
    (p : MvPolynomial V R) (hp : p.totalDegree < J) :
    evalAt X p = ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J),
      if E ⊆ X then difference E p else 0 := by
  classical
  simp only [difference_eq_sum_coeff]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hcard : d.support.card < J := (support_card_le_totalDegree p hd).trans_lt hp
  rw [evalAt_monomial]
  by_cases hsub : d.support ⊆ X
  · rw [ite_eq_left hsub]
    symm
    rw [Finset.sum_eq_single d.support]
    · simp [hsub]
    · intro E _ hE
      simp [Ne.symm hE]
    · simp [hcard]
  · rw [ite_eq_right hsub]
    symm
    apply Finset.sum_eq_zero
    intro E _
    by_cases he : d.support = E
    · subst E; simp [hsub]
    · simp [he]

/-- Boolean assignments retain all ambient variables, including unused ones. -/
def trueSet [Fintype V] (x : V → Bool) : Finset V :=
  Finset.univ.filter (fun i => x i = true)

omit [DecidableEq V] in
@[simp] theorem subset_trueSet [Fintype V] (E : Finset V) (x : V → Bool) :
    E ⊆ trueSet x ↔ ∀ i ∈ E, x i = true := by
  simp [Finset.subset_iff, trueSet]

/-- ETH Boolean finite differences over an arbitrary commutative ring.
The polynomial is allowed to depend on the assignment being summed. -/
theorem sum_eval_eq_sum_differences [Fintype V] {J : ℕ}
    (p : (V → Bool) → MvPolynomial V R)
    (hp : ∀ x, (p x).totalDegree < J) :
    (∑ x, evalAt (trueSet x) (p x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        (-1 : R) ^ (E.card - U.card) *
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            evalAt U (p x) := by
  classical
  conv_lhs =>
    arg 2
    ext x
    rw [evalAt_eq_sum_differences _ _ (hp x)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  simp only [difference, Finset.sum_filter, subset_trueSet]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Every retained Taylor coefficient is recovered using the same pair family.
The hypothesis is the precise degree cost: each formal correction variable carries Z. -/
theorem coeff_sum_eval_eq_sum_differences [Fintype V] {J j : ℕ}
    (P : (V → Bool) → Polynomial (MvPolynomial V R)) (hj : j < J)
    (hP : ∀ x, ((P x).coeff j).totalDegree ≤ j) :
    (∑ x, (P x).map (evalAt (trueSet x))).coeff j =
      (∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J),
        ∑ U ∈ E.powerset, Polynomial.C ((-1 : R) ^ (E.card - U.card)) *
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            (P x).map (evalAt U)).coeff j := by
  classical
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  exact sum_eval_eq_sum_differences (fun x => (P x).coeff j)
    (fun x => (hP x).trans_lt hj)

/-- The entire truncated Taylor polynomial, also for J = 0 and an empty variable type. -/
theorem truncated_sum_eval_eq_sum_differences [Fintype V] (J : ℕ)
    (P : (V → Bool) → Polynomial (MvPolynomial V R))
    (hP : ∀ x j, j < J → ((P x).coeff j).totalDegree ≤ j) :
    (∑ j ∈ Finset.range J, Polynomial.monomial j
      ((∑ x, (P x).map (evalAt (trueSet x))).coeff j)) =
    ∑ j ∈ Finset.range J, Polynomial.monomial j
      ((∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J),
        ∑ U ∈ E.powerset, Polynomial.C ((-1 : R) ^ (E.card - U.card)) *
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            (P x).map (evalAt U)).coeff j) := by
  classical
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_sum_eval_eq_sum_differences P (Finset.mem_range.mp hj)
    (fun x => hP x j (Finset.mem_range.mp hj))]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
