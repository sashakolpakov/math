import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointSparsify
import OAI.Algorithms.SubexponentialSAT.Encoding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Appendix A: smallest-width, largest-core selection and marked degrees. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority

open OAI.Algorithms.SubexponentialSAT.SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

/-- Number of width-`c` clauses containing a literal core. -/
def degree {V : Type*} [DecidableEq V] (F : CNF V) (c : ℕ) (H : Clause V) : ℕ :=
  (selected F c H).card

private def orderedClauses (F : CNF (Fin n)) : List (Clause (Fin n)) :=
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  F.sort r

@[simp] private theorem mem_orderedClauses (F : CNF (Fin n)) (C : Clause (Fin n)) :
    C ∈ orderedClauses F ↔ C ∈ F := by simp [orderedClauses]

@[simp] private theorem length_orderedClauses (F : CNF (Fin n)) :
    (orderedClauses F).length = F.card := by simp [orderedClauses]

/-- Enumerate clause/core pairs, never tuples of parameter-dependent size. -/
def candidates (F : CNF (Fin n)) : List (ℕ × Clause (Fin n)) :=
  (orderedClauses F).flatMap fun C =>
    (orderedClauses C.powerset).map fun H => (C.card, H)

@[simp] theorem mem_candidates (F : CNF (Fin n)) (c : ℕ) (H : Clause (Fin n)) :
    (c, H) ∈ candidates F ↔ ∃ C ∈ F, C.card = c ∧ H ⊆ C := by
  simp only [candidates, List.mem_flatMap, List.mem_map, mem_orderedClauses,
    Finset.mem_powerset, Prod.mk.injEq]
  constructor
  · rintro ⟨C, hC, K, hK, hcard, rfl⟩
    exact ⟨C, hC, hcard, hK⟩
  · rintro ⟨C, hC, hcard, hH⟩
    exact ⟨C, hC, H, hH, hcard, rfl⟩

theorem candidates_length_le (F : CNF (Fin n)) (k : ℕ)
    (hF : ∀ C ∈ F, C.card ≤ k) :
    (candidates F).length ≤ F.card * 2 ^ k := by
  simp only [candidates, List.length_flatMap, List.length_map, length_orderedClauses,
    Finset.card_powerset]
  calc
    ((orderedClauses F).map fun C => 2 ^ C.card).sum ≤
        ((orderedClauses F).map fun _ => 2 ^ k).sum := by
      apply List.sum_le_sum
      intro C hC
      exact Nat.pow_le_pow_right (by decide) (hF C ((mem_orderedClauses F C).mp hC))
    _ = F.card * 2 ^ k := by simp

/-- A coarse polynomial clause bound, sufficient for the search cost. -/
theorem clause_card_le (F : CNF (Fin n)) (k : ℕ)
    (hF : ∀ C ∈ F, C.card ≤ k) : F.card ≤ (k + 1) * (2 * n + 1) ^ k := by
  let enc := fun C : Clause (Fin n) => C.image Encoding.literalCode
  have hinj : Function.Injective enc := Finset.image_injective Encoding.literalCode_injective
  have hsub : F.image enc ⊆ (Finset.range (k + 1)).biUnion
      (fun j => (Finset.range (2 * n)).powersetCard j) := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    refine Finset.mem_biUnion.mpr ⟨D.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (hF D hD)), ?_⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Encoding.literalCode_lt l)
    · exact Finset.card_image_of_injective _ Encoding.literalCode_injective
  calc
    F.card = (F.image enc).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.range (k + 1)).biUnion
        (fun j => (Finset.range (2 * n)).powersetCard j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (k + 1)).card * (2 * n + 1) ^ k := by
      apply Finset.card_biUnion_le_card_mul
      intro j hj
      simp only [Finset.card_powersetCard, Finset.card_range]
      calc
        (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
        _ ≤ (2 * n + 1) ^ j := Nat.pow_le_pow_left (by omega) _
        _ ≤ (2 * n + 1) ^ k := Nat.pow_le_pow_right (by omega)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = (k + 1) * (2 * n + 1) ^ k := by rw [Finset.card_range]

/-- The threshold is tested by exact natural arithmetic. -/
def violatingCandidates (F : CNF (Fin n)) (M : ℕ) : List (ℕ × Clause (Fin n)) :=
  (candidates F).filter fun p =>
    decide (0 < p.2.card ∧ p.2.card < p.1 ∧ M ^ (p.1 - p.2.card) ≤ degree F p.1 p.2)

/-- The lexicographic key orders smaller widths first and larger cores first. -/
def select (F : CNF (Fin n)) (M : ℕ) : Option (ℕ × Clause (Fin n)) :=
  (violatingCandidates F M).argmin fun p =>
    (toLex (p.1, OrderDual.toDual p.2.card) : ℕ ×ₗ ℕᵒᵈ)

@[simp] theorem mem_violatingCandidates (F : CNF (Fin n)) (M c : ℕ)
    (H : Clause (Fin n)) :
    (c, H) ∈ violatingCandidates F M ↔
      (∃ C ∈ F, C.card = c ∧ H ⊆ C) ∧ 0 < H.card ∧ H.card < c ∧
        M ^ (c - H.card) ≤ degree F c H := by
  simp [violatingCandidates]

theorem violatingCandidates_length_le (F : CNF (Fin n)) (M k : ℕ)
    (hF : ∀ C ∈ F, C.card ≤ k) :
    (violatingCandidates F M).length ≤ (k + 1) * (2 * n + 1) ^ k * 2 ^ k :=
  (List.length_filter_le _ _).trans ((candidates_length_le F k hF).trans
    (Nat.mul_le_mul_right _ (clause_card_le F k hF)))

theorem select_spec {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (h : select F M = some (c, H)) :
    (∃ C ∈ F, C.card = c ∧ H ⊆ C) ∧ 0 < H.card ∧ H.card < c ∧
      M ^ (c - H.card) ≤ degree F c H := by
  have hm : (c, H) ∈ select F M := by simp [h]
  exact (mem_violatingCandidates F M c H).mp (List.argmin_mem hm)

theorem select_selected_card_ge_two {F : CNF (Fin n)} {M c : ℕ}
    {H : Clause (Fin n)} (hM : 2 ≤ M) (h : select F M = some (c, H)) :
    2 ≤ (selected F c H).card := by
  have hs := select_spec h
  have hpow : 1 < M ^ (c - H.card) :=
    Nat.one_lt_pow (Nat.sub_ne_zero_of_lt hs.2.2.1) hM
  exact (Nat.succ_le_of_lt hpow).trans hs.2.2.2

private theorem mem_violating_of_degree {F : CNF (Fin n)} {M c : ℕ}
    {H : Clause (Fin n)} (hM : 0 < M) (hH : 0 < H.card) (hc : H.card < c)
    (hd : M ^ (c - H.card) ≤ degree F c H) :
    (c, H) ∈ violatingCandidates F M := by
  apply (mem_violatingCandidates F M c H).mpr
  have hpos : 0 < (selected F c H).card := lt_of_lt_of_le (pow_pos hM _) hd
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  exact ⟨⟨C, (mem_selected.mp hC).1, (mem_selected.mp hC).2⟩, hH, hc, hd⟩

theorem select_priority {F : CNF (Fin n)} {M c d : ℕ} {H S : Clause (Fin n)}
    (hM : 0 < M) (h : select F M = some (c, H))
    (hS : 0 < S.card) (hd : S.card < d)
    (hdegree : M ^ (d - S.card) ≤ degree F d S) :
    c ≤ d ∧ (c = d → S.card ≤ H.card) := by
  have hs := mem_violating_of_degree hM hS hd hdegree
  have hmem : (c, H) ∈ select F M := by simp [h]
  have hle := List.le_of_mem_argmin hs hmem
  exact Prod.Lex.toLex_le_toLex'.mp hle

theorem smaller_width_degree_lt {F : CNF (Fin n)} {M c j : ℕ}
    {H S : Clause (Fin n)} (hM : 0 < M) (h : select F M = some (c, H))
    (hS : 0 < S.card) (hSj : S.card < j) (hj : j < c) :
    degree F j S < M ^ (j - S.card) := by
  by_contra hnot
  have hp := (select_priority hM h hS hSj (Nat.le_of_not_gt hnot)).1
  omega

theorem larger_core_degree_lt {F : CNF (Fin n)} {M c : ℕ}
    {H S : Clause (Fin n)} (hM : 0 < M) (h : select F M = some (c, H))
    (hHS : H.card < S.card) (hSc : S.card < c) :
    degree F c S < M ^ (c - S.card) := by
  by_contra hnot
  have hp := (select_priority hM h (by omega) hSc (Nat.le_of_not_gt hnot)).2 rfl
  omega

theorem select_none_degree_lt {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (hM : 0 < M) (h : select F M = none) (hH : 0 < H.card) (hc : H.card < c) :
    degree F c H < M ^ (c - H.card) := by
  by_contra hnot
  have hm := mem_violating_of_degree hM hH hc (Nat.le_of_not_gt hnot)
  have he : violatingCandidates F M = [] := List.argmin_eq_none.mp h
  simp [he] at hm


theorem select_eq_none_of_degrees {F : CNF (Fin n)} {M : ℕ}
    (h : ∀ (c : ℕ) (H : Clause (Fin n)), 0 < H.card → H.card < c →
      degree F c H < M ^ (c - H.card)) : select F M = none := by
  cases hs : select F M with
  | none => rfl
  | some p =>
    have hp := select_spec hs
    exact (Nat.not_lt_of_ge hp.2.2.2 (h p.1 p.2 hp.2.1 hp.2.2.1)).elim

/-- The local consequences of the source priority, independent of deterministic tie order. -/
structure Priority (F : CNF (Fin n)) (M c : ℕ) (H : Clause (Fin n)) : Prop where
  exists_clause : ∃ C ∈ F, C.card = c ∧ H ⊆ C
  core_nonempty : 0 < H.card
  core_proper : H.card < c
  threshold : M ^ (c - H.card) ≤ degree F c H
  minimum : ∀ {j : ℕ} (S : Clause (Fin n)), 0 < S.card → S.card < j → j < c →
    degree F j S < M ^ (j - S.card)
  maximum : ∀ S : Clause (Fin n), H.card < S.card → S.card < c →
    degree F c S < M ^ (c - S.card)

theorem Priority.spec {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (h : Priority F M c H) :
    (∃ C ∈ F, C.card = c ∧ H ⊆ C) ∧ 0 < H.card ∧ H.card < c ∧
      M ^ (c - H.card) ≤ degree F c H :=
  ⟨h.exists_clause, h.core_nonempty, h.core_proper, h.threshold⟩

theorem Priority.width_ge_two {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (h : Priority F M c H) : 2 ≤ c := by
  have hnonempty := h.core_nonempty
  have hproper := h.core_proper
  omega

theorem Priority.selected_card_ge_two {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (h : Priority F M c H) (hM : 2 ≤ M) : 2 ≤ (selected F c H).card := by
  have hpow := Nat.one_lt_pow (Nat.sub_ne_zero_of_lt h.core_proper) hM
  exact (Nat.succ_le_of_lt hpow).trans h.threshold

@[simp] theorem select_empty (M : ℕ) : select (∅ : CNF (Fin n)) M = none := by
  cases h : select (∅ : CNF (Fin n)) M with
  | none => rfl
  | some p =>
    obtain ⟨C, hC, _⟩ := (select_spec h).1
    simp at hC

@[simp] theorem select_singleton_empty (M : ℕ) :
    select ({∅} : CNF (Fin n)) M = none := by
  cases h : select ({∅} : CNF (Fin n)) M with
  | none => rfl
  | some p =>
    obtain ⟨⟨C, hC, hwidth, _⟩, hnonempty, hproper, _⟩ := select_spec h
    have hC' : C = ∅ := Finset.mem_singleton.mp hC
    simp only [hC', Finset.card_empty] at hwidth
    omega

theorem select_has_priority {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (hM : 0 < M) (h : select F M = some (c, H)) : Priority F M c H where
  exists_clause := (select_spec h).1
  core_nonempty := (select_spec h).2.1
  core_proper := (select_spec h).2.2.1
  threshold := (select_spec h).2.2.2
  minimum := fun _ hS hSj hj => smaller_width_degree_lt hM h hS hSj hj
  maximum := fun _ hHS hSc => larger_core_degree_lt hM h hHS hSc

theorem degree_mono {V : Type*} [DecidableEq V] {F G : CNF V}
    (hFG : F ⊆ G) (j : ℕ) (S : Clause V) : degree F j S ≤ degree G j S := by
  apply Finset.card_le_card
  intro C hC
  exact mem_selected.mpr ⟨hFG (mem_selected.mp hC).1, (mem_selected.mp hC).2⟩

theorem degree_union_le {V : Type*} [DecidableEq V] (F G : CNF V)
    (j : ℕ) (S : Clause V) : degree (F ∪ G) j S ≤ degree F j S + degree G j S := by
  unfold degree selected
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

private theorem degree_eq_zero_of_width {V : Type*} [DecidableEq V]
    {F : CNF V} {j : ℕ} (S : Clause V) (hF : ∀ C ∈ F, C.card ≠ j) :
    degree F j S = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  exact hF C (mem_selected.mp hC).1 (mem_selected.mp hC).2.1

theorem Priority.petals_degree_lt {F : CNF (Fin n)} {M c : ℕ} {H S : Clause (Fin n)}
    (hM : 0 < M) (h : Priority F M c H)
    (hS : 0 < S.card) (hSj : S.card < c - H.card) :
    degree (petals F c H) (c - H.card) S < M ^ (c - H.card - S.card) := by
  by_cases hzero : degree (petals F c H) (c - H.card) S = 0
  · rw [hzero]
    exact pow_pos hM _
  have hpos : 0 < (selected (petals F c H) (c - H.card) S).card :=
    Nat.pos_of_ne_zero hzero
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  obtain ⟨hP, _, hSP⟩ := mem_selected.mp hP
  obtain ⟨C, _, hCP⟩ := Finset.mem_image.mp hP
  have hHS : Disjoint H S := by
    apply Finset.disjoint_left.mpr
    intro l hlH hlS
    have hlP := hSP hlS
    rw [← hCP] at hlP
    exact (Finset.mem_sdiff.mp hlP).2 hlH
  have hcard : (H ∪ S).card = H.card + S.card := Finset.card_union_of_disjoint hHS
  have hHc := h.core_proper
  have hlarge := h.maximum (H ∪ S)
    (by omega) (by omega)
  have heq : selected (petals F c H) (c - H.card) S =
      (petals F c H).filter (fun P => S ⊆ P) := by
    ext P
    simp only [mem_selected, Finset.mem_filter]
    constructor
    · rintro ⟨hP, _, hSP⟩
      exact ⟨hP, hSP⟩
    · rintro ⟨hP, hSP⟩
      exact ⟨hP, petal_card hP, hSP⟩
  unfold degree at hlarge ⊢
  rw [heq, petals_filter_card F c H S hHS]
  simpa [hcard, Nat.sub_sub] using hlarge

/-- A marked `A` child may discard clauses; adding its single core preserves the bound. -/
theorem Priority.marked_degree_childA {F marked next : CNF (Fin n)} {M c j : ℕ}
    {H S : Clause (Fin n)} (hM : 2 ≤ M) (h : Priority F M c H)
    (hmarked : marked ⊆ F) (hnext : next ⊆ marked ∪ {H})
    (hS : 0 < S.card) (hSj : S.card < j)
    (hold : degree marked j S < 2 * M ^ (j - S.card)) :
    degree next j S < 2 * M ^ (j - S.card) := by
  have hcap := (degree_mono hnext j S).trans (degree_union_le marked {H} j S)
  by_cases hHj : H.card = j
  · have hsmall := h.minimum S hS hSj (by have hc := h.core_proper; omega)
    have hmarked' := degree_mono hmarked j S
    have hsingle : degree ({H} : CNF (Fin n)) j S ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hpow : 1 < M ^ (j - S.card) :=
      Nat.one_lt_pow (Nat.sub_ne_zero_of_lt hSj) hM
    omega
  · have hzero : degree ({H} : CNF (Fin n)) j S = 0 :=
      degree_eq_zero_of_width S (by simpa using hHj)
    omega

/-- Petals and false-core units preserve the bound at every marked `B` child. -/
theorem Priority.marked_degree_childB {F marked next : CNF (Fin n)} {M c j : ℕ}
    {H S : Clause (Fin n)} (hM : 2 ≤ M) (h : Priority F M c H)
    (hmarked : marked ⊆ F)
    (hnext : next ⊆ (marked ∪ petals F c H) ∪ negatedCoreUnits H)
    (hS : 0 < S.card) (hSj : S.card < j)
    (hold : degree marked j S < 2 * M ^ (j - S.card)) :
    degree next j S < 2 * M ^ (j - S.card) := by
  have hunits : degree (negatedCoreUnits H) j S = 0 := by
    apply degree_eq_zero_of_width S
    intro C hC
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hC
    simp only [Finset.card_singleton]
    omega
  have hcap := (degree_mono hnext j S).trans
    ((degree_union_le (marked ∪ petals F c H) (negatedCoreUnits H) j S).trans
      (Nat.add_le_add_right (degree_union_le marked (petals F c H) j S) _))
  by_cases hj : j = c - H.card
  · have hHc := h.core_nonempty
    have hsmall := h.minimum S hS hSj (by omega)
    have hmarked' := degree_mono hmarked j S
    have hpetals := h.petals_degree_lt (by omega) hS (by omega)
    rw [← hj] at hpetals
    omega
  · have hzero : degree (petals F c H) j S = 0 := by
      apply degree_eq_zero_of_width S
      intro P hP heq
      have hp := petal_card hP
      omega
    omega

theorem petals_degree_lt {F : CNF (Fin n)} {M c : ℕ} {H S : Clause (Fin n)}
    (hM : 0 < M) (h : select F M = some (c, H))
    (hS : 0 < S.card) (hSj : S.card < c - H.card) :
    degree (petals F c H) (c - H.card) S < M ^ (c - H.card - S.card) :=
  (select_has_priority hM h).petals_degree_lt hM hS hSj

theorem marked_degree_childA {F marked next : CNF (Fin n)} {M c j : ℕ}
    {H S : Clause (Fin n)} (hM : 2 ≤ M) (h : select F M = some (c, H))
    (hmarked : marked ⊆ F) (hnext : next ⊆ marked ∪ {H})
    (hS : 0 < S.card) (hSj : S.card < j)
    (hold : degree marked j S < 2 * M ^ (j - S.card)) :
    degree next j S < 2 * M ^ (j - S.card) :=
  (select_has_priority (by omega) h).marked_degree_childA hM hmarked hnext hS hSj hold

theorem marked_degree_childB {F marked next : CNF (Fin n)} {M c j : ℕ}
    {H S : Clause (Fin n)} (hM : 2 ≤ M) (h : select F M = some (c, H))
    (hmarked : marked ⊆ F)
    (hnext : next ⊆ (marked ∪ petals F c H) ∪ negatedCoreUnits H)
    (hS : 0 < S.card) (hSj : S.card < j)
    (hold : degree marked j S < 2 * M ^ (j - S.card)) :
    degree next j S < 2 * M ^ (j - S.card) :=
  (select_has_priority (by omega) h).marked_degree_childB hM hmarked hnext hS hSj hold

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
