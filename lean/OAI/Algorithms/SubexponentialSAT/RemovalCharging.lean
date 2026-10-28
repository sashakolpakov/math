import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.SunflowerBranch
import OAI.Algorithms.SubexponentialSAT.InsertionInvariant
import OAI.Algorithms.SubexponentialSAT.SparsificationConstants

namespace OAI.Algorithms

/-!
# Appendix A.2: charging removals to smaller insertions

The trace below records finite clause families before and after each replacement.
The cumulative insertion counter counts events, not distinct clauses.  Its
accounting identity therefore does not assume that reinsertion is impossible.
-/

namespace SubexponentialSAT.RemovalCharging

open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
/-- A finite relation covering its source gives an upper bound by the sum of
the sizes of its target fibers. No disjointness of fibers is required. -/
theorem card_le_mul_of_cover (s : Finset α) (t : Finset β)
    (r : α → β → Prop) [DecidableRel r] (M : ℕ)
    (hcover : ∀ a ∈ s, ∃ b ∈ t, r a b)
    (hcap : ∀ b ∈ t, (s.filter fun a => r a b).card ≤ M) :
    s.card ≤ M * t.card := by
  have hsub : s ⊆ t.biUnion (fun b => s.filter fun a => r a b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcover a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
  calc
    s.card ≤ (t.biUnion (fun b => s.filter fun a => r a b)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ t, (s.filter fun a => r a b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ t, M := Finset.sum_le_sum hcap
    _ = M * t.card := by simp [Nat.mul_comm]

/-- In particular, an actual single-valued charge with bounded fibers has the
same bound. -/
theorem card_le_mul_of_charge (s : Finset α) (t : Finset β) (charge : α → β)
    (M : ℕ) (hcharge : ∀ a ∈ s, charge a ∈ t)
    (hcap : ∀ b ∈ t, (s.filter fun a => charge a = b).card ≤ M) :
    s.card ≤ M * t.card :=
  card_le_mul_of_cover s t (fun a b => charge a = b) M
    (fun a ha => ⟨charge a, hcharge a ha, rfl⟩) hcap

abbrev Family (α : Type*) := Finset (Finset α)

def widthCount (F : Family α) (j : ℕ) : ℕ :=
  (F.filter fun C => C.card = j).card

def widthLiteralDegree (F : Family α) (j : ℕ) (a : α) : ℕ :=
  (F.filter fun C => C.card = j ∧ a ∈ C).card

def Antichain (F : Family α) : Prop :=
  ∀ C ∈ F, ∀ D ∈ F, C ⊆ D → C = D

omit [DecidableEq α] in
/-- Partition the new clauses of width below `j` by their exact widths. -/
theorem smaller_card_eq_sum_widthCount (F : Family α) (j : ℕ) :
    (F.filter fun C => C.card < j).card =
      ∑ i ∈ Finset.range j, widthCount F i := by
  symm
  simpa [widthCount] using
    Finset.sum_card_fiberwise_eq_card_filter F (Finset.range j) Finset.card

/-- Every removed width-`j` clause contains a nonempty new clause.  Its fiber
is bounded by the degree of any literal in that new clause. -/
theorem removed_widthCount_le (F R B : Family α) (j M : ℕ)
    (hRF : R ⊆ F)
    (hnew : ∀ Q ∈ B, Q.Nonempty)
    (hremove : ∀ C ∈ R, ∃ Q ∈ B, Q ⊂ C)
    (hdegree : ∀ a, widthLiteralDegree F j a ≤ M) :
    widthCount R j ≤ M * ∑ i ∈ Finset.range j, widthCount B i := by
  rw [← smaller_card_eq_sum_widthCount]
  apply card_le_mul_of_cover (R.filter fun C => C.card = j)
    (B.filter fun Q => Q.card < j) (fun C Q => Q ⊂ C) M
  · intro C hC
    obtain ⟨hCR, hwidth⟩ := Finset.mem_filter.mp hC
    obtain ⟨Q, hQB, hQC⟩ := hremove C hCR
    refine ⟨Q, Finset.mem_filter.mpr ⟨hQB, ?_⟩, hQC⟩
    exact hwidth ▸ Finset.card_lt_card hQC
  · intro Q hQ
    obtain ⟨a, ha⟩ := hnew Q (Finset.mem_filter.mp hQ).1
    calc
      ((R.filter fun C => C.card = j).filter fun C => Q ⊂ C).card ≤
          (F.filter fun C => C.card = j ∧ a ∈ C).card := by
        apply Finset.card_le_card
        intro C hC
        obtain ⟨hC, hQC⟩ := Finset.mem_filter.mp hC
        obtain ⟨hCR, hwidth⟩ := Finset.mem_filter.mp hC
        exact Finset.mem_filter.mpr
          ⟨hRF hCR, hwidth, (Finset.ssubset_iff_subset_ne.mp hQC).1 ha⟩
      _ ≤ M := hdegree a

/-- Summing per-literal bounds controls the number of live nonempty clauses. -/
theorem widthCount_le_universe_mul (F : Family α) (U : Finset α) (j M : ℕ)
    (hnonempty : ∀ C ∈ F, C.Nonempty)
    (hsupport : ∀ C ∈ F, C ⊆ U)
    (hdegree : ∀ a, widthLiteralDegree F j a ≤ M) :
    widthCount F j ≤ M * U.card := by
  apply card_le_mul_of_cover (F.filter fun C => C.card = j) U
    (fun C a => a ∈ C) M
  · intro C hC
    have hCF := (Finset.mem_filter.mp hC).1
    obtain ⟨a, ha⟩ := hnonempty C hCF
    exact ⟨a, hsupport C hCF ha, ha⟩
  · intro a _
    simpa [widthLiteralDegree, Finset.filter_filter] using hdegree a

/-- A finite replacement trace.  All fields are local properties of actual
finite sets; no cumulative counting conclusion is assumed. -/
structure Trace (α : Type*) [DecidableEq α] (T : ℕ) where
  formula : ℕ → Family α
  inserted : ℕ → Family α
  next_subset : ∀ t < T, formula (t + 1) ⊆ formula t ∪ inserted t
  inserted_live : ∀ t < T, inserted t ⊆ formula (t + 1)
  fresh : ∀ t < T, Disjoint (formula t) (inserted t)
  inserted_nonempty : ∀ t < T, ∀ Q ∈ inserted t, Q.Nonempty
  removed_subset : ∀ t < T, ∀ C ∈ formula t,
    C ∉ formula (t + 1) → ∃ Q ∈ inserted t, Q ⊂ C

namespace Trace

variable {T : ℕ} (tr : Trace α T)

/-- Clauses introduced by the trace that are still alive. Root clauses start
untracked; survival is tested against the actual next formula. -/
def live : ℕ → Family α
  | 0 => ∅
  | t + 1 => (live t ∩ tr.formula (t + 1)) ∪ tr.inserted t

@[simp] theorem live_zero : tr.live 0 = ∅ := rfl

@[simp] theorem live_succ (t : ℕ) :
    tr.live (t + 1) = (tr.live t ∩ tr.formula (t + 1)) ∪ tr.inserted t := rfl

theorem live_subset_formula (t : ℕ) (ht : t ≤ T) : tr.live t ⊆ tr.formula t := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact (Finset.mem_inter.mp hC).2
    · exact tr.inserted_live t (by omega) hC

theorem live_nonempty (t : ℕ) (ht : t ≤ T) :
    ∀ C ∈ tr.live t, C.Nonempty := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact ih (by omega) C (Finset.mem_inter.mp hC).1
    · exact tr.inserted_nonempty t (by omega) C hC

/-- Every tracked clause has a genuine earlier insertion event. -/
theorem live_has_origin {t : ℕ} {C : Finset α} (hC : C ∈ tr.live t) :
    ∃ s < t, C ∈ tr.inserted s := by
  induction t with
  | zero => simp at hC
  | succ t ih =>
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨s, hs, hCs⟩ := ih (Finset.mem_inter.mp hC).1
      exact ⟨s, by omega, hCs⟩
    · exact ⟨t, Nat.lt_succ_self _, hC⟩

/-- Cumulative individual insertion events, including clauses later removed. -/
def insertions (t j : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, widthCount (tr.inserted s) j

def removed (t : ℕ) : Family α := tr.live t \ tr.formula (t + 1)

def removals (t j : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, widthCount (tr.removed s) j

/-- The absorbing subset is inserted strictly after the removed clause's
original insertion event, even though absorption and subset insertion share
the same replacement step. -/
theorem removed_has_later_subset {t : ℕ} (ht : t < T)
    {C : Finset α} (hC : C ∈ tr.removed t) :
    ∃ s < t, C ∈ tr.inserted s ∧ ∃ Q ∈ tr.inserted t, Q ⊂ C := by
  obtain ⟨hCL, hCF⟩ := Finset.mem_sdiff.mp hC
  obtain ⟨s, hs, hCs⟩ := tr.live_has_origin hCL
  exact ⟨s, hs, hCs,
    tr.removed_subset t ht C (tr.live_subset_formula t (by omega) hCL) hCF⟩

theorem removed_has_subset {t : ℕ} (ht : t < T)
    {C : Finset α} (hC : C ∈ tr.removed t) :
    ∃ Q ∈ tr.inserted t, Q ⊂ C := by
  obtain ⟨s, hs, hCs, hQ⟩ := tr.removed_has_later_subset ht hC
  exact hQ

/-- Fix exactly one absorbing new clause for each removal event. This finite
witness selection is used only for counting, never as a SAT truth oracle. -/
noncomputable def charge (t : ℕ) (ht : t < T) (C : Finset α) : Finset α :=
  if hC : C ∈ tr.removed t then (tr.removed_has_subset ht hC).choose else ∅

theorem charge_spec {t : ℕ} (ht : t < T) {C : Finset α}
    (hC : C ∈ tr.removed t) :
    tr.charge t ht C ∈ tr.inserted t ∧ tr.charge t ht C ⊂ C := by
  rw [charge, dite_eq_left hC]
  exact (tr.removed_has_subset ht hC).choose_spec

/-- One inserted clause receives at most the per-literal degree bound in
charges from removed clauses of any fixed width. -/
theorem charge_fiber_bound (t j M : ℕ) (ht : t < T)
    (hdegree : ∀ a, widthLiteralDegree (tr.live t) j a ≤ M)
    {Q : Finset α} (hQ : Q ∈ tr.inserted t) :
    ((tr.removed t).filter fun C => C.card = j ∧ tr.charge t ht C = Q).card ≤ M := by
  classical
  obtain ⟨a, ha⟩ := tr.inserted_nonempty t ht Q hQ
  calc
    ((tr.removed t).filter fun C => C.card = j ∧ tr.charge t ht C = Q).card ≤
        ((tr.live t).filter fun C => C.card = j ∧ a ∈ C).card := by
      apply Finset.card_le_card
      intro C hC
      obtain ⟨hCR, hwidth, hcharge⟩ := Finset.mem_filter.mp hC
      have hQC := (tr.charge_spec ht hCR).2
      rw [hcharge] at hQC
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hCR).1, hwidth,
        (Finset.ssubset_iff_subset_ne.mp hQC).1 ha⟩
    _ ≤ M := hdegree a

/-- The one-step conservation law for insertion events. -/
theorem accounting_step (t j : ℕ) (ht : t < T) :
    widthCount (tr.live (t + 1)) j + widthCount (tr.removed t) j =
      widthCount (tr.live t) j + widthCount (tr.inserted t) j := by
  let A := (tr.live t).filter fun C => C.card = j
  let B := (tr.inserted t).filter fun C => C.card = j
  have hsplit : (tr.live (t + 1)).filter (fun C => C.card = j) =
      (A ∩ tr.formula (t + 1)) ∪ B := by
    ext C
    simp only [live_succ, Finset.mem_filter, Finset.mem_union, Finset.mem_inter, A, B]
    tauto
  have hremoved : (tr.removed t).filter (fun C => C.card = j) =
      A \ tr.formula (t + 1) := by
    ext C
    simp only [removed, Finset.mem_filter, Finset.mem_sdiff, A]
    tauto
  have hd : Disjoint (A ∩ tr.formula (t + 1)) B := by
    apply Finset.disjoint_left.mpr
    intro C hCA hCB
    have hCF : C ∈ tr.formula t := tr.live_subset_formula t (by omega)
      (Finset.mem_filter.mp (Finset.mem_inter.mp hCA).1).1
    exact Finset.disjoint_left.mp (tr.fresh t ht) hCF (Finset.mem_filter.mp hCB).1
  have hp := Finset.card_sdiff_add_card_inter A (tr.formula (t + 1))
  change ((tr.live (t + 1)).filter _).card + ((tr.removed t).filter _).card =
    A.card + B.card
  rw [hsplit, hremoved, Finset.card_union_of_disjoint hd]
  omega

/-- Telescoping counts insertions by their fate: still live or removed once.
This remains valid even without a no-reinsertion theorem. -/
theorem accounting (t j : ℕ) (ht : t ≤ T) :
    tr.insertions t j = widthCount (tr.live t) j + tr.removals t j := by
  induction t with
  | zero => simp [insertions, removals, widthCount]
  | succ t ih =>
    have hi := ih (by omega)
    have hs := tr.accounting_step t j (by omega)
    simp only [insertions, removals, Finset.sum_range_succ] at hi ⊢
    omega

theorem removed_count_le (t j M : ℕ) (ht : t < T)
    (hdegree : ∀ a, widthLiteralDegree (tr.live t) j a ≤ M) :
    widthCount (tr.removed t) j ≤
      M * ∑ i ∈ Finset.range j, widthCount (tr.inserted t) i := by
  apply removed_widthCount_le (tr.live t) (tr.removed t) (tr.inserted t) j M
  · exact Finset.sdiff_subset
  · exact tr.inserted_nonempty t ht
  · intro C hC
    obtain ⟨hCL, hCF⟩ := Finset.mem_sdiff.mp hC
    exact tr.removed_subset t ht C (tr.live_subset_formula t (by omega) hCL) hCF
  · exact hdegree

/-- The cumulative charging bound over an explicit finite trace. -/
theorem insertion_bound (j M : ℕ) (U : Finset α)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ a, widthLiteralDegree (tr.live t) j a ≤ M) :
    tr.insertions T j ≤ M * (U.card +
      ∑ i ∈ Finset.range j, tr.insertions T i) := by
  have hfinal : widthCount (tr.live T) j ≤ M * U.card :=
    widthCount_le_universe_mul (tr.live T) U j M
      (tr.live_nonempty T le_rfl) hsupport (hdegree T le_rfl)
  have hremoved : tr.removals T j ≤
      ∑ t ∈ Finset.range T, M * ∑ i ∈ Finset.range j,
        widthCount (tr.inserted t) i := by
    apply Finset.sum_le_sum
    intro t ht
    have htT := Finset.mem_range.mp ht
    exact tr.removed_count_le t j M htT (hdegree t (by omega))
  have hswap : (∑ t ∈ Finset.range T, M * ∑ i ∈ Finset.range j,
        widthCount (tr.inserted t) i) =
      M * ∑ i ∈ Finset.range j, tr.insertions T i := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    rfl
  rw [hswap] at hremoved
  rw [tr.accounting T j le_rfl, Nat.mul_add]
  exact Nat.add_le_add hfinal hremoved

/-- Equation (A.1), with a literal universe of size at most `2*n`. -/
theorem insertion_bound_two_n (j L n : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ a, widthLiteralDegree (tr.live t) j a ≤ L + 1) :
    tr.insertions T j ≤ (L + 1) * (2 * n +
      ∑ i ∈ Finset.range j, tr.insertions T i) := by
  exact (tr.insertion_bound j (L + 1) U hsupport hdegree).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hU _))

theorem insertions_zero : tr.insertions T 0 = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro Q hQ hcard
  have hp := (tr.inserted_nonempty t (Finset.mem_range.mp ht) Q hQ).card_pos
  omega

/-- Repeated replacement always leaves a live descendant of every old clause. -/
theorem descendant {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T)
    {C : Finset α} (hC : C ∈ tr.formula a) :
    ∃ D ∈ tr.formula b, D ⊆ C := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base =>
    intro _
    exact ⟨C, hC, Finset.Subset.refl _⟩
  | succ b hab ih =>
    intro hb
    obtain ⟨D, hD, hDC⟩ := ih (by omega)
    by_cases hnext : D ∈ tr.formula (b + 1)
    · exact ⟨D, hnext, hDC⟩
    · obtain ⟨Q, hQ, hQD⟩ := tr.removed_subset b (by omega) D hD hnext
      exact ⟨Q, tr.inserted_live b (by omega) hQ,
        (Finset.ssubset_iff_subset_ne.mp hQD).1.trans hDC⟩

/-- A removed clause cannot return to a later antichain: its strict descendant
persists and would absorb it. -/
theorem removed_never_returns
    (hanti : ∀ t ≤ T, Antichain (tr.formula t))
    {t s : ℕ} (ht : t < T) (hts : t + 1 ≤ s) (hs : s ≤ T)
    {C : Finset α} (hC : C ∈ tr.formula t) (hremoved : C ∉ tr.formula (t + 1)) :
    C ∉ tr.formula s := by
  obtain ⟨Q, hQ, hQC⟩ := tr.removed_subset t ht C hC hremoved
  obtain ⟨D, hD, hDQ⟩ := tr.descendant hts hs (tr.inserted_live t ht hQ)
  obtain ⟨hQCsub, hQCne⟩ := Finset.ssubset_iff_subset_ne.mp hQC
  intro hCs
  have hDC : D = C := hanti s hs D hD C hCs (hDQ.trans hQCsub)
  have hCQ : C ⊆ Q := hDC ▸ hDQ
  exact hQCne (Finset.Subset.antisymm hQCsub hCQ)

theorem removed_never_reinserted
    (hanti : ∀ t ≤ T, Antichain (tr.formula t))
    {t s : ℕ} (ht : t < T) (hts : t + 1 ≤ s) (hs : s < T)
    {C : Finset α} (hC : C ∈ tr.formula t) (hremoved : C ∉ tr.formula (t + 1)) :
    C ∉ tr.inserted s := by
  intro hnew
  exact tr.removed_never_returns hanti ht (by omega) (by omega) hC hremoved
    (tr.inserted_live s hs hnew)

/-- Derive the degree premise of the charging theorem from actual batches and
the minimum-width pre-insertion bounds, using `InsertionInvariant`. -/
theorem degree_bound (L d : ℕ → ℕ)
    (hlt : ∀ t < T, ∀ C ∈ tr.inserted t, C.card < d t)
    (hone : ∀ t < T, InsertionInvariant.OnePerLiteral (tr.inserted t))
    (hpre : ∀ t < T, ∀ j, j < d t → ∀ a,
      widthLiteralDegree (tr.formula t) j a ≤ L j) :
    ∀ t ≤ T, ∀ j a, widthLiteralDegree (tr.live t) j a ≤ L j + 1 := by
  intro t ht
  induction t with
  | zero =>
    intro j a
    simp [widthLiteralDegree]
  | succ t ih =>
    have htT : t < T := by omega
    let s : InsertionInvariant.State α :=
      ⟨tr.formula t, tr.live t, tr.live_subset_formula t (by omega)⟩
    let u : InsertionInvariant.State α :=
      ⟨tr.formula (t + 1), tr.live (t + 1), tr.live_subset_formula (t + 1) ht⟩
    let e : InsertionInvariant.BatchStep s u := {
      selectedWidth := d t
      inserted := tr.inserted t
      inserted_lt := hlt t htT
      onePerLiteral := hone t htT
      child_subset := tr.next_subset t htT
      tracked_eq := by
        change tr.live (t + 1) = (tr.live t ∪ tr.inserted t) ∩ tr.formula (t + 1)
        ext C
        simp only [live_succ, Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (⟨hCL, hCF⟩ | hCB)
          · exact ⟨Or.inl hCL, hCF⟩
          · exact ⟨Or.inr hCB, tr.inserted_live t htT hCB⟩
        · rintro ⟨hCL | hCB, hCF⟩
          · exact Or.inl ⟨hCL, hCF⟩
          · exact Or.inr hCB }
    have hepre : InsertionInvariant.PreInsertionBound L s e.selectedWidth :=
      hpre t htT
    have hs : InsertionInvariant.DegreeInvariant L s := ih (by omega)
    exact e.preserves_degreeInvariant hepre hs

/-- The cumulative bound with the per-state invariant discharged by the
one-per-literal and minimum-width properties of the branching trace. -/
theorem insertion_bound_of_minimum_width (L d : ℕ → ℕ) (n j : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hlt : ∀ t < T, ∀ C ∈ tr.inserted t, C.card < d t)
    (hone : ∀ t < T, InsertionInvariant.OnePerLiteral (tr.inserted t))
    (hpre : ∀ t < T, ∀ i, i < d t → ∀ a,
      widthLiteralDegree (tr.formula t) i a ≤ L i) :
    tr.insertions T j ≤ (L j + 1) *
      (2 * n + ∑ i ∈ Finset.range j, tr.insertions T i) := by
  apply tr.insertion_bound_two_n j (L j) n U hU hsupport
  intro t ht a
  exact tr.degree_bound L d hlt hone hpre t ht j a

end Trace

section Absorption

variable {V : Type*} [DecidableEq V] {T : ℕ}

/-- Antichains are maintained by actual `SAT.absorb` replacements. -/
theorem replacement_history_antichain (F S B : ℕ → SAT.CNF V)
    (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, F (t + 1) = SunflowerBranch.replace (F t) (S t) (B t)) :
    ∀ t ≤ T, SunflowerBranch.Antichain (F t) := by
  intro t ht
  cases t with
  | zero => exact hzero
  | succ t =>
    rw [hstep t (by omega)]
    exact SunflowerBranch.replacement_antichain _ _ _

/-- Build the charging trace from literal-set replacement followed by actual
absorption. Freshness, survival, and strict-subset removal witnesses are proved,
not postulated, using `SunflowerBranch`'s finite-set lemmas. -/
def ofReplacements (F S B : ℕ → SAT.CNF V)
    (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, F (t + 1) = SunflowerBranch.replace (F t) (S t) (B t))
    (hbatch : ∀ t < T, SunflowerBranch.Antichain (B t))
    (hnew : ∀ t < T, ∀ Q ∈ B t, ∃ C ∈ F t, Q ⊂ C)
    (hselected : ∀ t < T, ∀ C ∈ S t, ∃ Q ∈ B t, Q ⊂ C)
    (hnonempty : ∀ t < T, ∀ Q ∈ B t, Q.Nonempty) :
    Trace (SAT.Literal V) T := by
  have hanti := replacement_history_antichain F S B hzero hstep
  exact {
    formula := F
    inserted := B
    next_subset := by
      intro t ht
      rw [hstep t ht]
      exact SunflowerBranch.replace_subset _ _ _
    inserted_live := by
      intro t ht
      rw [hstep t ht]
      exact SunflowerBranch.inserted_survive (hanti t (by omega))
        (hbatch t ht) (hnew t ht)
    fresh := by
      intro t ht
      apply Finset.disjoint_left.mpr
      intro C hCF hCB
      exact SunflowerBranch.new_not_mem_old (hanti t (by omega)) (hnew t ht) hCB hCF
    inserted_nonempty := hnonempty
    removed_subset := by
      intro t ht C hCF hgone
      rw [hstep t ht] at hgone
      exact SunflowerBranch.removed_contains_inserted (hanti t (by omega))
        (hselected t ht) hCF hgone }

/-- No-reinsertion for the concrete absorption histories used by the count. -/
theorem replacement_removed_never_returns (F S B : ℕ → SAT.CNF V)
    (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, F (t + 1) = SunflowerBranch.replace (F t) (S t) (B t))
    (hbatch : ∀ t < T, SunflowerBranch.Antichain (B t))
    (hnew : ∀ t < T, ∀ Q ∈ B t, ∃ C ∈ F t, Q ⊂ C)
    (hselected : ∀ t < T, ∀ C ∈ S t, ∃ Q ∈ B t, Q ⊂ C)
    (hnonempty : ∀ t < T, ∀ Q ∈ B t, Q.Nonempty)
    {t s : ℕ} (ht : t < T) (hts : t + 1 ≤ s) (hs : s ≤ T)
    {C : SAT.Clause V} (hC : C ∈ F t) (hremoved : C ∉ F (t + 1)) : C ∉ F s := by
  let tr := ofReplacements F S B hzero hstep hbatch hnew hselected hnonempty
  exact tr.removed_never_returns (replacement_history_antichain F S B hzero hstep)
    ht hts hs hC hremoved

/-- An actual choice of one of the two literal-set sunflower children, recording
the inserted batch and the selected width. -/
inductive SunflowerStep (F : SAT.CNF V) : SAT.CNF V → SAT.CNF V → ℕ → Prop
  | core {d : ℕ} (s : SunflowerBranch.Sunflower V d)
      (hsub : SunflowerBranch.clauses s.core s.petals ⊆ F) :
      SunflowerStep F (SunflowerBranch.childA F s.core s.petals) {s.core} d
  | petals {d : ℕ} (s : SunflowerBranch.Sunflower V d)
      (hsub : SunflowerBranch.clauses s.core s.petals ⊆ F) :
      SunflowerStep F (SunflowerBranch.childB F s.core s.petals) s.petals d

namespace SunflowerStep

variable {F G B : SAT.CNF V} {d : ℕ} (h : SunflowerStep F G B d)

include h

theorem antichain : SunflowerBranch.Antichain G := by
  cases h with
  | core => exact SunflowerBranch.antichain_absorb _
  | petals => exact SunflowerBranch.antichain_absorb _

theorem subset : G ⊆ F ∪ B := by
  cases h with
  | core s hsub =>
    intro C hC
    have hm := SAT.absorb_subset _ hC
    rcases Finset.mem_insert.mp hm with heq | hrem
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr heq)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hrem).1
  | petals s hsub => exact SunflowerBranch.replace_subset _ _ _

theorem nonempty : ∀ Q ∈ B, Q.Nonempty := by
  cases h with
  | core s hsub =>
    intro Q hQ
    have heq := Finset.mem_singleton.mp hQ
    exact heq ▸ s.core_nonempty
  | petals s hsub =>
    intro Q hQ
    exact s.petal_nonempty hQ

theorem width_lt : ∀ Q ∈ B, Q.card < d := by
  cases h with
  | core s hsub =>
    intro Q hQ
    have heq := Finset.mem_singleton.mp hQ
    exact heq ▸ s.core_card_lt
  | petals s hsub =>
    intro Q hQ
    exact s.petal_card_lt hQ

theorem onePerLiteral : InsertionInvariant.OnePerLiteral B := by
  cases h with
  | core s hsub => exact InsertionInvariant.onePerLiteral_singleton _
  | petals s hsub =>
    exact InsertionInvariant.onePerLiteral_of_pairwiseDisjoint s.pairwise_disjoint

theorem survives (hF : SunflowerBranch.Antichain F) : B ⊆ G := by
  cases h with
  | core s hsub =>
    exact Finset.singleton_subset_iff.mpr (s.core_mem_childA hF hsub)
  | petals s hsub => exact s.petals_subset_childB hF hsub

theorem fresh (hF : SunflowerBranch.Antichain F) : Disjoint F B := by
  apply Finset.disjoint_left.mpr
  intro Q hQF hQB
  cases h with
  | core s hsub =>
    have heq := Finset.mem_singleton.mp hQB
    exact s.core_new hF hsub (heq ▸ hQF)
  | petals s hsub => exact s.petal_new hF hsub hQB hQF

theorem removed_subset (hF : SunflowerBranch.Antichain F)
    {C : SAT.Clause V} (hCF : C ∈ F) (hCG : C ∉ G) :
    ∃ Q ∈ B, Q ⊂ C := by
  cases h with
  | core s hsub =>
    exact ⟨s.core, Finset.mem_singleton_self _, s.removed_childA_contains_core hF hCF hCG⟩
  | petals s hsub => exact s.removed_childB_contains_petal hF hCF hCG

end SunflowerStep

theorem sunflower_history_antichain (F B : ℕ → SAT.CNF V) (d : ℕ → ℕ)
    (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, SunflowerStep (F t) (F (t + 1)) (B t) (d t)) :
    ∀ t ≤ T, SunflowerBranch.Antichain (F t) := by
  intro t ht
  cases t with
  | zero => exact hzero
  | succ t => exact (hstep t (by omega)).antichain

/-- A path of actual sunflower choices automatically supplies every local
set-theoretic hypothesis of the charging trace. -/
def ofSunflowerSteps (F B : ℕ → SAT.CNF V) (d : ℕ → ℕ)
    (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, SunflowerStep (F t) (F (t + 1)) (B t) (d t)) :
    Trace (SAT.Literal V) T := by
  have hanti := sunflower_history_antichain F B d hzero hstep
  exact {
    formula := F
    inserted := B
    next_subset := fun t ht => (hstep t ht).subset
    inserted_live := fun t ht => (hstep t ht).survives (hanti t (by omega))
    fresh := fun t ht => (hstep t ht).fresh (hanti t (by omega))
    inserted_nonempty := fun t ht => (hstep t ht).nonempty
    removed_subset := fun t ht _ => (hstep t ht).removed_subset (hanti t (by omega)) }

end Absorption

section SATLiteralUniverse

variable {V : Type*} [DecidableEq V] [Fintype V] {T : ℕ}

/-- An explicit finite universe containing the two signs of every variable. -/
def literalUniverse : Finset (SAT.Literal V) :=
  Finset.univ.image fun p : V × Bool => ⟨p.1, p.2⟩

theorem mem_literalUniverse (l : SAT.Literal V) : l ∈ literalUniverse (V := V) := by
  apply Finset.mem_image.mpr
  refine ⟨(l.variable, l.positive), Finset.mem_univ _, ?_⟩
  cases l
  rfl

theorem literalUniverse_card_le : (literalUniverse (V := V)).card ≤
    2 * Fintype.card V := by
  calc
    (literalUniverse (V := V)).card ≤ (Finset.univ : Finset (V × Bool)).card :=
      Finset.card_image_le
    _ = 2 * Fintype.card V := by simp [Nat.mul_comm]

/-- Equation (A.1) for actual signed SAT literals, with no abstract universe
or final-live-count premise remaining. -/
theorem insertion_bound_cnf (tr : Trace (SAT.Literal V) T)
    (L d : ℕ → ℕ) (j : ℕ)
    (hlt : ∀ t < T, ∀ C ∈ tr.inserted t, C.card < d t)
    (hone : ∀ t < T, InsertionInvariant.OnePerLiteral (tr.inserted t))
    (hpre : ∀ t < T, ∀ i, i < d t → ∀ a,
      widthLiteralDegree (tr.formula t) i a ≤ L i) :
    tr.insertions T j ≤ (L j + 1) *
      (2 * Fintype.card V + ∑ i ∈ Finset.range j, tr.insertions T i) := by
  apply tr.insertion_bound_of_minimum_width L d (Fintype.card V) j
    literalUniverse literalUniverse_card_le
  · intro C _ a _
    exact mem_literalUniverse a
  · exact hlt
  · exact hone
  · exact hpre

/-- The cumulative insertion bound for a finite sequence of actual
`SAT.absorb` replacements. The remaining local hypotheses are exactly the
batch and minimum-width properties supplied by sunflower branching. -/
theorem insertion_bound_cnf_of_replacements (F S B : ℕ → SAT.CNF V)
    (L d : ℕ → ℕ) (j : ℕ)
    (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, F (t + 1) = SunflowerBranch.replace (F t) (S t) (B t))
    (hbatch : ∀ t < T, SunflowerBranch.Antichain (B t))
    (hnew : ∀ t < T, ∀ Q ∈ B t, ∃ C ∈ F t, Q ⊂ C)
    (hselected : ∀ t < T, ∀ C ∈ S t, ∃ Q ∈ B t, Q ⊂ C)
    (hnonempty : ∀ t < T, ∀ Q ∈ B t, Q.Nonempty)
    (hlt : ∀ t < T, ∀ C ∈ B t, C.card < d t)
    (hone : ∀ t < T, InsertionInvariant.OnePerLiteral (B t))
    (hpre : ∀ t < T, ∀ i, i < d t → ∀ a,
      widthLiteralDegree (F t) i a ≤ L i) :
    (∑ t ∈ Finset.range T, widthCount (B t) j) ≤ (L j + 1) *
      (2 * Fintype.card V + ∑ i ∈ Finset.range j,
        ∑ t ∈ Finset.range T, widthCount (B t) i) := by
  let tr := ofReplacements F S B hzero hstep hbatch hnew hselected hnonempty
  exact insertion_bound_cnf tr L d j hlt hone hpre

/-- Equation (A.1) for a genuine finite minimum-width sunflower path. All
capacity, survivor-count, freshness, and absorption premises have been proved
from the path, rather than included in the conclusion's hypotheses. -/
theorem insertion_bound_sunflower_path (F B : ℕ → SAT.CNF V) (z d : ℕ → ℕ)
    (j : ℕ) (hz : ∀ i, 2 ≤ i → 2 ≤ z i)
    (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, SunflowerStep (F t) (F (t + 1)) (B t) (d t))
    (hminimum : ∀ t < T, InsertionInvariant.MinimumWidth z (F t) (d t)) :
    (∑ t ∈ Finset.range T, widthCount (B t) j) ≤
      (InsertionInvariant.thresholdDegreeBound z j + 1) *
        (2 * Fintype.card V + ∑ i ∈ Finset.range j,
          ∑ t ∈ Finset.range T, widthCount (B t) i) := by
  let tr := ofSunflowerSteps F B d hzero hstep
  apply insertion_bound_cnf tr (InsertionInvariant.thresholdDegreeBound z) d j
  · intro t ht
    exact (hstep t ht).width_lt
  · intro t ht
    exact (hstep t ht).onePerLiteral
  · intro t ht
    exact InsertionInvariant.minimumWidth_preInsertionBound
      (s := InsertionInvariant.initial (F t)) hz (hminimum t ht)

end SATLiteralUniverse

section PathBudgets

/-- The threshold formula agrees with the recursive constants at every
positive width. Width zero is treated separately by `insertions_zero`. -/
theorem thresholdDegreeBound_eq_L (M j : ℕ) (hj : 1 ≤ j) :
    InsertionInvariant.thresholdDegreeBound (SparsificationConstants.z M) j =
      SparsificationConstants.L M j := by
  by_cases hone : j = 1
  · subst j
    simp
  · exact (SparsificationConstants.L_eq_threshold_formula M j (by omega)).symm

omit [DecidableEq α] in
theorem card_eq_sum_widthCount_of_lt (B : Family α) (k : ℕ)
    (hwidth : ∀ C ∈ B, C.card < k) :
    B.card = ∑ j ∈ Finset.range k, widthCount B j := by
  rw [← smaller_card_eq_sum_widthCount]
  congr 1
  exact (Finset.filter_eq_self.mpr hwidth).symm

theorem SunflowerStep.batch_nonempty {V : Type*} [DecidableEq V]
    {F G B : SAT.CNF V} {d : ℕ} (h : SunflowerStep F G B d) : B.Nonempty := by
  cases h with
  | core s hsub => exact Finset.singleton_nonempty _
  | petals s hsub => exact s.petals_nonempty

variable {n T : ℕ}

/-- Actual sunflower paths satisfy the cumulative insertion recurrence for
the concrete constants chosen in Appendix A.3. -/
theorem sunflower_path_cumulative_bound
    (F B : ℕ → SAT.CNF (Fin n)) (d : ℕ → ℕ) (M r : ℕ)
    (hM : 2 ≤ M) (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, SunflowerStep (F t) (F (t + 1)) (B t) (d t))
    (hminimum : ∀ t < T,
      InsertionInvariant.MinimumWidth (SparsificationConstants.z M) (F t) (d t)) :
    (∑ j ∈ Finset.range (r + 1), ∑ t ∈ Finset.range T, widthCount (B t) j) ≤
      SparsificationConstants.C M r * n := by
  let N : ℕ → ℕ := fun j => ∑ t ∈ Finset.range T, widthCount (B t) j
  let tr := ofSunflowerSteps F B d hzero hstep
  have hNzero : N 0 = 0 := tr.insertions_zero
  have hcharge : ∀ j, 1 ≤ j → N j ≤ (SparsificationConstants.L M j + 1) *
      (2 * n + ∑ i ∈ Finset.range j, N i) := by
    intro j hj
    have h := insertion_bound_sunflower_path F B (SparsificationConstants.z M) d j
      (fun i hi => SparsificationConstants.threshold_ge_two M i hM hi)
      hzero hstep hminimum
    simpa only [thresholdDegreeBound_eq_L M j hj, Fintype.card_fin] using h
  exact SparsificationConstants.cumulative_insertions_le M n N hNzero hcharge r

/-- Every branch inserts at least one smaller clause, so the cumulative
insertion budget bounds the number of branching steps on an actual path. -/
theorem sunflower_path_depth_bound
    (F B : ℕ → SAT.CNF (Fin n)) (d : ℕ → ℕ) (M k : ℕ)
    (hM : 2 ≤ M) (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, SunflowerStep (F t) (F (t + 1)) (B t) (d t))
    (hminimum : ∀ t < T,
      InsertionInvariant.MinimumWidth (SparsificationConstants.z M) (F t) (d t))
    (hlower : ∀ t < T, 2 ≤ d t) (hupper : ∀ t < T, d t ≤ k) :
    T ≤ SparsificationConstants.C M (k - 1) * n := by
  by_cases hT : T = 0
  · subst T
    exact Nat.zero_le _
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT
  have hk : 1 ≤ k := by
    have h₁ := hlower 0 hTpos
    have h₂ := hupper 0 hTpos
    omega
  have hc := sunflower_path_cumulative_bound F B d M (k - 1) hM hzero hstep hminimum
  rw [Nat.sub_add_cancel hk] at hc
  calc
    T = ∑ _t ∈ Finset.range T, 1 := by simp
    _ ≤ ∑ t ∈ Finset.range T, (B t).card := by
      apply Finset.sum_le_sum
      intro t ht
      exact (hstep t (Finset.mem_range.mp ht)).batch_nonempty.card_pos
    _ = ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range k, widthCount (B t) j := by
      apply Finset.sum_congr rfl
      intro t ht
      apply card_eq_sum_widthCount_of_lt
      intro C hC
      exact lt_of_lt_of_le ((hstep t (Finset.mem_range.mp ht)).width_lt C hC)
        (hupper t (Finset.mem_range.mp ht))
    _ = ∑ j ∈ Finset.range k, ∑ t ∈ Finset.range T, widthCount (B t) j :=
      Finset.sum_comm
    _ ≤ SparsificationConstants.C M (k - 1) * n := hc

/-- Count the B-choices whose selected branching width is exactly `w`. -/
def BChoicesAtWidth (side : ℕ → Bool) (d : ℕ → ℕ) (T w : ℕ) : Finset ℕ :=
  (Finset.range T).filter fun t => side t = true ∧ d t = w

/-- Each width-`w` B-choice accounts for a full threshold-sized batch among
all insertions below width `w`. -/
theorem B_choices_width_insertion_budget
    (B : ℕ → SAT.CNF (Fin n)) (side : ℕ → Bool) (d : ℕ → ℕ) (M w : ℕ)
    (hwidth : ∀ t < T, ∀ C ∈ B t, C.card < d t)
    (hcard : ∀ t < T, side t = true → (B t).card = SparsificationConstants.z M (d t)) :
    (BChoicesAtWidth side d T w).card * SparsificationConstants.z M w ≤
      ∑ j ∈ Finset.range w, ∑ t ∈ Finset.range T, widthCount (B t) j := by
  let s := BChoicesAtWidth side d T w
  have hs : ∀ t ∈ s, t < T ∧ side t = true ∧ d t = w := by
    intro t ht
    obtain ⟨ht, hside, hd⟩ := Finset.mem_filter.mp ht
    exact ⟨Finset.mem_range.mp ht, hside, hd⟩
  calc
    s.card * SparsificationConstants.z M w = ∑ t ∈ s, (B t).card := by
      symm
      apply Finset.sum_const_nat
      intro t ht
      rw [hcard t (hs t ht).1 (hs t ht).2.1, (hs t ht).2.2]
    _ = ∑ t ∈ s, ∑ j ∈ Finset.range w, widthCount (B t) j := by
      apply Finset.sum_congr rfl
      intro t ht
      apply card_eq_sum_widthCount_of_lt
      intro C hC
      have h := hwidth t (hs t ht).1 C hC
      rwa [(hs t ht).2.2] at h
    _ ≤ ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range w, widthCount (B t) j :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ j ∈ Finset.range w, ∑ t ∈ Finset.range T, widthCount (B t) j :=
      Finset.sum_comm

/-- The integral B-choice bound for an actual path. Grouping by selected
width makes all per-width insertion charges disjoint as choice events. -/
theorem sunflower_path_B_choices_bound
    (F B : ℕ → SAT.CNF (Fin n)) (d : ℕ → ℕ) (side : ℕ → Bool) (M k : ℕ)
    (hM : 2 ≤ M) (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, SunflowerStep (F t) (F (t + 1)) (B t) (d t))
    (hminimum : ∀ t < T,
      InsertionInvariant.MinimumWidth (SparsificationConstants.z M) (F t) (d t))
    (hlower : ∀ t < T, 2 ≤ d t) (hupper : ∀ t < T, d t ≤ k)
    (hcard : ∀ t < T, side t = true → (B t).card = SparsificationConstants.z M (d t)) :
    ((Finset.range T).filter fun t => side t = true).card ≤ k * n / M := by
  let b := fun w => (BChoicesAtWidth side d T w).card
  have hinsert : ∀ w ∈ Finset.Icc 2 k,
      b w * SparsificationConstants.z M w ≤ SparsificationConstants.C M (w - 1) * n := by
    intro w hw
    have hwlo := (Finset.mem_Icc.mp hw).1
    have hc := sunflower_path_cumulative_bound F B d M (w - 1) hM hzero hstep hminimum
    rw [Nat.sub_add_cancel (show 1 ≤ w by omega)] at hc
    exact (B_choices_width_insertion_budget B side d M w
      (fun t ht => (hstep t ht).width_lt) hcard).trans hc
  have hsum := SparsificationConstants.B_choices_sum_mul_le M n (Finset.Icc 2 k) b
    (fun w hw => (Finset.mem_Icc.mp hw).1) hinsert
  have hcount : ((Finset.range T).filter fun t => side t = true).card =
      ∑ w ∈ Finset.Icc 2 k, b w := by
    have hmap : (((Finset.range T).filter fun t => side t = true) : Set ℕ).MapsTo d
        (Finset.Icc 2 k) := by
      intro t ht
      have htT := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      exact Finset.mem_Icc.mpr ⟨hlower t htT, hupper t htT⟩
    simpa only [b, BChoicesAtWidth, Finset.filter_filter] using
      Finset.card_eq_sum_card_fiberwise hmap
  have hsize : (Finset.Icc 2 k).card ≤ k := by
    rw [Nat.card_Icc]
    omega
  apply (Nat.le_div_iff_mul_le (show 0 < M by omega)).mpr
  rw [hcount]
  exact hsum.trans (Nat.mul_le_mul_right n hsize)

/-- Combined finite-path interface for the deterministic sparsification tree. -/
theorem sunflower_path_budgets
    (F B : ℕ → SAT.CNF (Fin n)) (d : ℕ → ℕ) (side : ℕ → Bool) (M k : ℕ)
    (hM : 2 ≤ M) (hzero : SunflowerBranch.Antichain (F 0))
    (hstep : ∀ t < T, SunflowerStep (F t) (F (t + 1)) (B t) (d t))
    (hminimum : ∀ t < T,
      InsertionInvariant.MinimumWidth (SparsificationConstants.z M) (F t) (d t))
    (hlower : ∀ t < T, 2 ≤ d t) (hupper : ∀ t < T, d t ≤ k)
    (hcard : ∀ t < T, side t = true → (B t).card = SparsificationConstants.z M (d t)) :
    T ≤ SparsificationConstants.C M (k - 1) * n ∧
      ((Finset.range T).filter fun t => side t = true).card ≤ k * n / M :=
  ⟨sunflower_path_depth_bound F B d M k hM hzero hstep hminimum hlower hupper,
    sunflower_path_B_choices_bound F B d side M k hM hzero hstep hminimum hlower hupper hcard⟩

end PathBudgets

end SubexponentialSAT.RemovalCharging

end OAI.Algorithms
