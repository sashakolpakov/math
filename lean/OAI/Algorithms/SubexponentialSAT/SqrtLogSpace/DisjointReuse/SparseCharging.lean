import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import OAI.Algorithms.SubexponentialSAT.RemovalCharging
import OAI.Algorithms.SubexponentialSAT.BranchTree
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority

/-! Appendix A, insertion recurrence and the resulting path budgets. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging

open scoped BigOperators

section FiniteCharging

variable {α : Type*} [DecidableEq α]

/-- Charge each removed marked clause to an inserted strict subset. Fibers may
overlap; their width-sensitive bounds are precisely those from marked priority. -/
theorem removed_card_le (marked removed inserted : Finset (Finset α)) (j M : ℕ)
    (hremoved : removed ⊆ marked)
    (hnonempty : ∀ Q ∈ inserted, Q.Nonempty)
    (hcharge : ∀ C ∈ removed, ∃ Q ∈ inserted, Q ⊂ C)
    (hdegree : ∀ Q ∈ inserted, 0 < Q.card → Q.card < j →
      (marked.filter fun C => C.card = j ∧ Q ⊆ C).card ≤ 2 * M ^ (j - Q.card)) :
    (removed.filter fun C => C.card = j).card ≤
      2 * ∑ i ∈ Finset.range j,
        M ^ (j - i) * (inserted.filter fun Q => Q.card = i).card := by
  let s := removed.filter fun C => C.card = j
  let t := inserted.filter fun Q => Q.card < j
  have hcover : s ⊆ t.biUnion (fun Q => s.filter fun C => Q ⊆ C) := by
    intro C hC
    obtain ⟨hCR, hCj⟩ := Finset.mem_filter.mp hC
    obtain ⟨Q, hQI, hQC⟩ := hcharge C hCR
    apply Finset.mem_biUnion.mpr
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQI, hCj ▸ Finset.card_lt_card hQC⟩,
      Finset.mem_filter.mpr ⟨hC, (Finset.ssubset_iff_subset_ne.mp hQC).1⟩⟩
  have hfiber : ∀ Q ∈ t, (s.filter fun C => Q ⊆ C).card ≤ 2 * M ^ (j - Q.card) := by
    intro Q hQ
    obtain ⟨hQI, hQj⟩ := Finset.mem_filter.mp hQ
    apply le_trans _ (hdegree Q hQI (hnonempty Q hQI).card_pos hQj)
    apply Finset.card_le_card
    intro C hC
    obtain ⟨hCs, hQC⟩ := Finset.mem_filter.mp hC
    obtain ⟨hCR, hCj⟩ := Finset.mem_filter.mp hCs
    exact Finset.mem_filter.mpr ⟨hremoved hCR, hCj, hQC⟩
  calc
    s.card ≤ (t.biUnion fun Q => s.filter fun C => Q ⊆ C).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ Q ∈ t, (s.filter fun C => Q ⊆ C).card := Finset.card_biUnion_le
    _ ≤ ∑ Q ∈ t, 2 * M ^ (j - Q.card) := Finset.sum_le_sum hfiber
    _ = 2 * ∑ i ∈ Finset.range j,
        M ^ (j - i) * (inserted.filter fun Q => Q.card = i).card := by
      have h := Finset.sum_fiberwise_eq_sum_filter' inserted (Finset.range j)
        Finset.card (fun i => 2 * M ^ (j - i))
      simp only [Finset.mem_range] at h
      change (∑ Q ∈ inserted.filter (fun Q => Q.card < j), 2 * M ^ (j - Q.card)) = _
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_assoc, mul_comm, mul_left_comm]

end FiniteCharging

def depthConstant (k M : ℕ) : ℕ :=
  4 * ∑ j ∈ Finset.range (k - 1), (3 * M) ^ j

def rightConstant (k : ℕ) : ℕ :=
  4 * ∑ j ∈ Finset.range (k - 1), 3 ^ j

/-- The recurrence in source equation `spar-insertions`, indexed from width one. -/
theorem insertion_le (M n k : ℕ) (N : ℕ → ℕ)
    (hrec : ∀ j < k - 1,
      N (j + 1) ≤ 4 * n * M ^ j +
        2 * ∑ i ∈ Finset.range j, M ^ (j - i) * N (i + 1)) :
    ∀ j < k - 1, N (j + 1) ≤ 4 * (3 * M) ^ j * n := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have hsum : (∑ i ∈ Finset.range j, M ^ (j - i) * N (i + 1)) ≤
        4 * n * M ^ j * ∑ i ∈ Finset.range j, 3 ^ i := by
      calc
        _ ≤ ∑ i ∈ Finset.range j, M ^ (j - i) * (4 * (3 * M) ^ i * n) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Nat.mul_le_mul_left _
            (ih i (Finset.mem_range.mp hi) ((Finset.mem_range.mp hi).trans hj))
        _ = 4 * n * M ^ j * ∑ i ∈ Finset.range j, 3 ^ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hpow : M ^ (j - i) * M ^ i = M ^ j := by
            rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt (Finset.mem_range.mp hi))]
          rw [mul_pow]
          calc
            _ = 4 * n * (M ^ (j - i) * M ^ i) * 3 ^ i := by ring
            _ = _ := by rw [hpow]
    have hgeom : (∑ i ∈ Finset.range j, 3 ^ i) * 2 + 1 = 3 ^ j :=
      geom_sum_mul_add (2 : ℕ) j
    calc
      N (j + 1) ≤ 4 * n * M ^ j +
          2 * ∑ i ∈ Finset.range j, M ^ (j - i) * N (i + 1) := hrec j hj
      _ ≤ 4 * n * M ^ j +
          2 * (4 * n * M ^ j * ∑ i ∈ Finset.range j, 3 ^ i) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 2 hsum) _
      _ = 4 * n * M ^ j * ((∑ i ∈ Finset.range j, 3 ^ i) * 2 + 1) := by ring
      _ = 4 * (3 * M) ^ j * n := by rw [hgeom, mul_pow]; ring

/-- Every edge inserts at least one clause; summing the sharp per-width bounds
therefore bounds a path's number of edges. -/
theorem depth_le (M n k T : ℕ) (N : ℕ → ℕ)
    (hsteps : T ≤ ∑ j ∈ Finset.range (k - 1), N (j + 1))
    (hN : ∀ j < k - 1, N (j + 1) ≤ 4 * (3 * M) ^ j * n) :
    T ≤ depthConstant k M * n := by
  calc
    T ≤ ∑ j ∈ Finset.range (k - 1), N (j + 1) := hsteps
    _ ≤ ∑ j ∈ Finset.range (k - 1), 4 * (3 * M) ^ j * n :=
      Finset.sum_le_sum fun j hj => hN j (Finset.mem_range.mp hj)
    _ = depthConstant k M * n := by
      simp only [depthConstant, ← Finset.sum_mul, ← Finset.mul_sum]

/-- Count B-edges by their petal width. The integral multiplicative form
retains the exact bound without truncating division. -/
theorem right_steps_mul_le (M n k : ℕ) (hM : 0 < M) (b : ℕ → ℕ)
    (hinsert : ∀ j < k - 1, b j * M ^ (j + 1) ≤ 4 * (3 * M) ^ j * n) :
    (∑ j ∈ Finset.range (k - 1), b j) * M ≤ rightConstant k * n := by
  have hwidth : ∀ j < k - 1, b j * M ≤ 4 * 3 ^ j * n := by
    intro j hj
    apply Nat.le_of_mul_le_mul_right (c := M ^ j) _ (pow_pos hM j)
    simpa [pow_succ, mul_pow, mul_assoc, mul_comm, mul_left_comm] using hinsert j hj
  calc
    (∑ j ∈ Finset.range (k - 1), b j) * M =
        ∑ j ∈ Finset.range (k - 1), b j * M := Finset.sum_mul _ _ _
    _ ≤ ∑ j ∈ Finset.range (k - 1), 4 * 3 ^ j * n :=
      Finset.sum_le_sum fun j hj => hwidth j (Finset.mem_range.mp hj)
    _ = rightConstant k * n := by
      simp only [rightConstant, ← Finset.sum_mul, ← Finset.mul_sum]

section Trace

open RemovalCharging

variable {α : Type*} [DecidableEq α] {T : ℕ}

/-- Count actual edges by their insertion events, grouped by positive width. -/
theorem trace_steps_le_insertions (tr : Trace α T) (k : ℕ)
    (hbatch : ∀ t < T, (tr.inserted t).Nonempty)
    (hwidth : ∀ t < T, ∀ C ∈ tr.inserted t, C.card < k) :
    T ≤ ∑ j ∈ Finset.range (k - 1), tr.insertions T (j + 1) := by
  have hsplit : ∀ t < T, (∑ j ∈ Finset.range (k - 1),
      widthCount (tr.inserted t) (j + 1)) = (tr.inserted t).card := by
    intro t ht
    calc
      _ = ∑ j ∈ Finset.Ico 1 k, widthCount (tr.inserted t) j := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp [Nat.add_comm]
      _ = ((tr.inserted t).filter fun C => C.card ∈ Finset.Ico 1 k).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ = (tr.inserted t).card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro C hC
        exact Finset.mem_Ico.mpr
          ⟨(tr.inserted_nonempty t ht C hC).card_pos, hwidth t ht C hC⟩
  calc
    T = ∑ _t ∈ Finset.range T, 1 := by simp
    _ ≤ ∑ t ∈ Finset.range T, (tr.inserted t).card :=
      Finset.sum_le_sum fun t ht => (hbatch t (Finset.mem_range.mp ht)).card_pos
    _ = ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range (k - 1),
        widthCount (tr.inserted t) (j + 1) :=
      Finset.sum_congr rfl fun t ht => (hsplit t (Finset.mem_range.mp ht)).symm
    _ = ∑ j ∈ Finset.range (k - 1), tr.insertions T (j + 1) := by
      rw [Finset.sum_comm]
      rfl

/-- Nonempty strict-subset replacements never remove an inserted unit clause. -/
theorem trace_units_le (tr : Trace α T) (U : Finset α)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U) : tr.insertions T 1 ≤ U.card := by
  have hremoved : tr.removals T 1 = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro C hC
    obtain ⟨hCR, hC1⟩ := Finset.mem_filter.mp hC
    obtain ⟨Q, hQI, hQC⟩ := tr.removed_has_subset (Finset.mem_range.mp ht) hCR
    have hpos := (tr.inserted_nonempty t (Finset.mem_range.mp ht) Q hQI).card_pos
    have hlt := Finset.card_lt_card hQC
    omega
  rw [tr.accounting T 1 le_rfl, hremoved, Nat.add_zero]
  have hdeg : ∀ a, widthLiteralDegree (tr.live T) 1 a ≤ 1 := by
    intro a
    calc
      _ ≤ ({({a} : Finset α)} : Finset (Finset α)).card := by
        apply Finset.card_le_card
        intro C hC
        obtain ⟨_, hC1, ha⟩ := Finset.mem_filter.mp hC
        obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hC1
        have hab : a = b := Finset.mem_singleton.mp ha
        simp [hab]
      _ = 1 := Finset.card_singleton _
  simpa using widthCount_le_universe_mul (tr.live T) U 1 1
    (tr.live_nonempty T le_rfl) hsupport hdeg

/-- Equation `spar-insertions` for the actual insertion and removal events of
a finite path; the marked-degree hypothesis is supplied by priority. -/
theorem trace_insertion_recurrence (tr : Trace α T) (M n k : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card)) :
    ∀ q < k - 1, tr.insertions T (q + 1) ≤ 4 * n * M ^ q +
      2 * ∑ i ∈ Finset.range q, M ^ (q - i) * tr.insertions T (i + 1) := by
  intro q hq
  cases q with
  | zero =>
    have hu := (trace_units_le tr U hsupport).trans hU
    simpa using hu.trans (show 2 * n ≤ 4 * n by omega)
  | succ q =>
    have hj : q + 1 + 1 < k := by omega
    have hfinal : widthCount (tr.live T) (q + 1 + 1) ≤
        4 * n * M ^ (q + 1) := by
      have hdeg : ∀ a, widthLiteralDegree (tr.live T) (q + 1 + 1) a ≤
          2 * M ^ (q + 1) := by
        intro a
        simpa [widthLiteralDegree] using
          hdegree T le_rfl (q + 1 + 1) hj {a} (by simp) (by simp)
      calc
        _ ≤ (2 * M ^ (q + 1)) * U.card :=
          widthCount_le_universe_mul (tr.live T) U _ _
            (tr.live_nonempty T le_rfl) hsupport hdeg
        _ ≤ (2 * M ^ (q + 1)) * (2 * n) := Nat.mul_le_mul_left _ hU
        _ = 4 * n * M ^ (q + 1) := by ring
    have hrem : tr.removals T (q + 1 + 1) ≤
        2 * ∑ i ∈ Finset.range (q + 1 + 1),
          M ^ (q + 1 + 1 - i) * tr.insertions T i := by
      calc
        _ ≤ ∑ t ∈ Finset.range T,
            2 * ∑ i ∈ Finset.range (q + 1 + 1),
              M ^ (q + 1 + 1 - i) * widthCount (tr.inserted t) i := by
          apply Finset.sum_le_sum
          intro t ht
          apply removed_card_le (tr.live t) (tr.removed t) (tr.inserted t)
          · exact Finset.sdiff_subset
          · exact tr.inserted_nonempty t (Finset.mem_range.mp ht)
          · intro C hC
            exact tr.removed_has_subset (Finset.mem_range.mp ht) hC
          · intro S _ hS hSj
            exact hdegree t (Nat.le_of_lt (Finset.mem_range.mp ht)) _ hj S hS hSj
        _ = 2 * ∑ i ∈ Finset.range (q + 1 + 1),
            M ^ (q + 1 + 1 - i) * tr.insertions T i := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Trace.insertions, Finset.mul_sum]
    rw [Finset.sum_range_succ'] at hrem
    simp only [tr.insertions_zero, Nat.mul_zero, Nat.add_zero,
      Nat.add_sub_add_right] at hrem
    rw [tr.accounting T (q + 1 + 1) le_rfl]
    exact Nat.add_le_add hfinal hrem

/-- The sharp source bound, now applied to an actual finite replacement trace. -/
theorem trace_insertions_le (tr : Trace α T) (M n k : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card)) :
    ∀ j < k - 1, tr.insertions T (j + 1) ≤ 4 * (3 * M) ^ j * n :=
  insertion_le M n k (tr.insertions T)
    (trace_insertion_recurrence tr M n k U hU hsupport hdegree)

/-- The source depth bound counts every edge of the same concrete path. -/
theorem trace_depth_le (tr : Trace α T) (M n k : ℕ) (U : Finset α)
    (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hbatch : ∀ t < T, (tr.inserted t).Nonempty)
    (hwidth : ∀ t < T, ∀ C ∈ tr.inserted t, C.card < k)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card)) :
    T ≤ depthConstant k M * n :=
  depth_le M n k T (tr.insertions T) (trace_steps_le_insertions tr k hbatch hwidth)
    (trace_insertions_le tr M n k U hU hsupport hdegree)

/-- A B-edge of petal width `w` consumes at least `M^w` actual insertion events. -/
theorem trace_right_steps_mul_le (tr : Trace α T) (M n k : ℕ) (hM : 0 < M)
    (U : Finset α) (hU : U.card ≤ 2 * n)
    (hsupport : ∀ C ∈ tr.live T, C ⊆ U)
    (hdegree : ∀ t ≤ T, ∀ j < k, ∀ S : Finset α, 0 < S.card → S.card < j →
      ((tr.live t).filter fun C => C.card = j ∧ S ⊆ C).card ≤
        2 * M ^ (j - S.card))
    (b : ℕ → Bool) (w : ℕ → ℕ)
    (hwidth : ∀ t < T, b t = true → 0 < w t ∧ w t < k)
    (hbatch : ∀ t < T, b t = true → M ^ w t ≤ widthCount (tr.inserted t) (w t)) :
    ((Finset.range T).filter fun t => b t = true).card * M ≤ rightConstant k * n := by
  let R := (Finset.range T).filter fun t => b t = true
  let counts := fun j => (R.filter fun t => w t = j + 1).card
  have hsplit : R.card = ∑ j ∈ Finset.range (k - 1), counts j := by
    symm
    calc
      _ = ∑ j ∈ Finset.Ico 1 k, (R.filter fun t => w t = j).card := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp [counts, Nat.add_comm]
      _ = (R.filter fun t => w t ∈ Finset.Ico 1 k).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ = R.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro t ht
        obtain ⟨ht, hb⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_Ico.mpr (hwidth t (Finset.mem_range.mp ht) hb)
  change R.card * M ≤ rightConstant k * n
  rw [hsplit]
  apply right_steps_mul_le M n k hM counts
  intro j hj
  apply le_trans _ (trace_insertions_le tr M n k U hU hsupport hdegree j hj)
  calc
    counts j * M ^ (j + 1) = ∑ t ∈ R.filter (fun t => w t = j + 1),
        M ^ (j + 1) := by simp [counts]
    _ ≤ ∑ t ∈ R.filter (fun t => w t = j + 1),
        widthCount (tr.inserted t) (j + 1) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨htR, hw⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht, hb⟩ := Finset.mem_filter.mp htR
      simpa only [hw] using hbatch t (Finset.mem_range.mp ht) hb
    _ ≤ ∑ t ∈ Finset.range T, widthCount (tr.inserted t) (j + 1) :=
      Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

end Trace

section SelectedTrace

open RemovalCharging DisjointBranch

variable {n T : ℕ}

theorem path_invariants (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    ∀ t ≤ T, SunflowerBranch.Antichain (F t) ∧
      (∀ C ∈ F t, ¬ C.IsTautology) ∧ SAT.WidthAtMost k (F t) := by
  intro t ht
  induction t with
  | zero => exact ⟨hanti, hnt, hwidth⟩
  | succ t ih =>
    have htT : t < T := by omega
    obtain ⟨_, hn, hw⟩ := ih (by omega)
    have hs := (hselect t htT).spec
    have hsel : (selected (F t) (c t) (H t)).Nonempty := by
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      exact ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩⟩
    rw [hnext t htT]
    cases hb : b t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨childA_antichain _ _ _, childA_not_tautological hn hsel,
        childA_widthAtMost hw hsel hs.2.2.1⟩
    · simp only [↓reduceIte]
      exact ⟨childB_antichain _ _ _, childB_not_tautological hn,
        childB_widthAtMost hw hsel (Finset.card_pos.mp hs.2.1) hs.2.2.1⟩

/-- The concrete replacement trace induced by a selected formula path. -/
def selectedTrace (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    Trace (SAT.Literal (Fin n)) T where
  formula := F
  inserted := fun t => if b t then insertedB (F t) (c t) (H t) else {H t}
  next_subset := by
    intro t ht
    rw [hnext t ht]
    cases hb : b t <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact childA_subset _ _ _
    · exact childB_subset _ _ _
  inserted_live := by
    intro t ht
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have hs := (hselect t ht).spec
    have hsel : (selected (F t) (c t) (H t)).Nonempty := by
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      exact ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩⟩
    rw [hnext t ht]
    cases hb : b t <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact Finset.singleton_subset_iff.mpr (core_mem_childA hinv.1 hsel hs.2.2.1)
    · exact insertedB_subset_childB hinv.1 hsel (Finset.card_pos.mp hs.2.1)
        hs.2.2.1 hinv.2.1
  fresh := by
    intro t ht
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have hs := (hselect t ht).spec
    cases hb : b t <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · apply Finset.disjoint_singleton_right.mpr
      apply core_new hinv.1 _ hs.2.2.1
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      exact ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩⟩
    · exact insertedB_disjoint _ _ _
  inserted_nonempty := by
    intro t ht Q hQ
    have hs := (hselect t ht).spec
    cases hb : b t <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hQ
    · have hQH := Finset.mem_singleton.mp hQ
      rw [hQH]
      exact Finset.card_pos.mp hs.2.1
    · exact insertedB_nonempty hs.2.2.1 hQ
  removed_subset := by
    intro t ht C hC hgone
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have hs := (hselect t ht).spec
    rw [hnext t ht] at hgone
    cases hb : b t <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hgone ⊢
    · exact ⟨H t, Finset.mem_singleton_self _,
        removed_childA_contains_core hinv.1 hs.2.2.1 hC hgone⟩
    · exact removed_childB_contains_inserted hinv.1 (Finset.card_pos.mp hs.2.1) hC hgone

/-- Priority bounds marked subset degrees at every prefix of a selected path. -/
theorem trace_marked_degree (tr : Trace (SAT.Literal (Fin n)) T) (M : ℕ)
    (hM : 2 ≤ M)
    (hstep : ∀ t < T, ∃ c H,
      SparsePriority.Priority (tr.formula t) M c H ∧
        (tr.inserted t = {H} ∨ tr.inserted t = insertedB (tr.formula t) c H)) :
    ∀ t ≤ T, ∀ (j : ℕ) (S : SAT.Clause (Fin n)), 0 < S.card → S.card < j →
      SparsePriority.degree (tr.live t) j S < 2 * M ^ (j - S.card) := by
  intro t ht
  induction t with
  | zero =>
    intro j S _ _
    change (selected ∅ j S).card < 2 * M ^ (j - S.card)
    simp only [selected, Finset.filter_empty, Finset.card_empty]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  | succ t ih =>
    intro j S hS hSj
    have htT : t < T := by omega
    obtain ⟨c, H, hsel, hA | hB⟩ := hstep t htT
    · apply SparsePriority.Priority.marked_degree_childA hM hsel
        (tr.live_subset_formula t (by omega))
      · intro C hC
        rcases Finset.mem_union.mp hC with hC | hC
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hC).1)
        · exact Finset.mem_union.mpr (Or.inr (hA ▸ hC))
      · exact hS
      · exact hSj
      · exact ih (by omega) j S hS hSj
    · apply SparsePriority.Priority.marked_degree_childB hM hsel
        (tr.live_subset_formula t (by omega))
      · intro C hC
        rcases Finset.mem_union.mp hC with hC | hC
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hC).1)))
        · rw [hB] at hC
          rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hC).1 with hP | hU
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hP)))
          · exact Finset.mem_union.mpr (Or.inr hU)
      · exact hS
      · exact hSj
      · exact ih (by omega) j S hS hSj

/-- Every actual selected path has the draft's linear depth bound. -/
theorem selected_path_depth_le (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ) (hM : 2 ≤ M)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    T ≤ depthConstant k M * n := by
  let tr := selectedTrace F c H b M k hselect hnext hanti hnt hwidth
  have hstep : ∀ t < T, ∃ c H,
      SparsePriority.Priority (tr.formula t) M c H ∧
        (tr.inserted t = {H} ∨ tr.inserted t = insertedB (tr.formula t) c H) := by
    intro t ht
    refine ⟨c t, H t, hselect t ht, ?_⟩
    cases hb : b t <;> simp [tr, selectedTrace, hb]
  apply trace_depth_le tr M n k (literalUniverse (V := Fin n))
  · simpa using (literalUniverse_card_le (V := Fin n))
  · intro C _ a _
    exact mem_literalUniverse a
  · intro t ht
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    change (if b t then insertedB (F t) (c t) (H t) else {H t}).Nonempty
    cases hb : b t
    · simp
    · simp only [↓reduceIte]
      obtain ⟨C, hCF, hCc, hHC⟩ := hs.1
      refine ⟨C \ H t, petals_subset_insertedB hinv.1 (Finset.card_pos.mp hs.2.1) ?_⟩
      exact Finset.mem_image.mpr ⟨C, mem_selected.mpr ⟨hCF, hCc, hHC⟩, rfl⟩
  · intro t ht Q hQ
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    obtain ⟨C, hCF, hCc, _⟩ := hs.1
    have hck : c t ≤ k := hCc ▸ hinv.2.2 C hCF
    change Q ∈ (if b t then insertedB (F t) (c t) (H t) else {H t}) at hQ
    cases hb : b t <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hQ
    · rw [Finset.mem_singleton.mp hQ]
      exact hs.2.2.1.trans_le hck
    · exact (insertedB_width_lt (Finset.card_pos.mp hs.2.1) hs.2.2.1 hQ).trans_le hck
  · intro t ht j _ S hS hSj
    simpa [SparsePriority.degree, selected] using
      (trace_marked_degree tr M hM hstep t ht j S hS hSj).le

/-- The B-choice bound for the same actual selected path. -/
theorem selected_path_right_steps_mul_le (F : ℕ → SAT.CNF (Fin n)) (c : ℕ → ℕ)
    (H : ℕ → SAT.Clause (Fin n)) (b : ℕ → Bool) (M k : ℕ) (hM : 2 ≤ M)
    (hselect : ∀ t < T, SparsePriority.Priority (F t) M (c t) (H t))
    (hnext : ∀ t < T, F (t + 1) =
      if b t then childB (F t) (c t) (H t) else childA (F t) (c t) (H t))
    (hanti : SunflowerBranch.Antichain (F 0))
    (hnt : ∀ C ∈ F 0, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k (F 0)) :
    ((Finset.range T).filter fun t => b t = true).card * M ≤ rightConstant k * n := by
  let tr := selectedTrace F c H b M k hselect hnext hanti hnt hwidth
  have hstep : ∀ t < T, ∃ c H,
      SparsePriority.Priority (tr.formula t) M c H ∧
        (tr.inserted t = {H} ∨ tr.inserted t = insertedB (tr.formula t) c H) := by
    intro t ht
    refine ⟨c t, H t, hselect t ht, ?_⟩
    cases hb : b t <;> simp [tr, selectedTrace, hb]
  refine trace_right_steps_mul_le tr M n k (by omega) (literalUniverse (V := Fin n))
      ?_ ?_ ?_ b (fun t => c t - (H t).card) ?_ ?_
  · simpa using (literalUniverse_card_le (V := Fin n))
  · intro C _ a _
    exact mem_literalUniverse a
  · intro t ht j _ S hS hSj
    simpa [SparsePriority.degree, selected] using
      (trace_marked_degree tr M hM hstep t ht j S hS hSj).le
  · intro t ht _
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    obtain ⟨C, hCF, hCc, _⟩ := hs.1
    have hck : c t ≤ k := hCc ▸ hinv.2.2 C hCF
    exact ⟨Nat.sub_pos_of_lt hs.2.2.1,
      (Nat.sub_lt (hs.2.1.trans hs.2.2.1) hs.2.1).trans_le hck⟩
  · intro t ht hb
    have hs := (hselect t ht).spec
    have hinv := path_invariants F c H b M k hselect hnext hanti hnt hwidth t (by omega)
    have h := hs.2.2.2.trans
      (selected_card_le_insertedB_width hinv.1 (Finset.card_pos.mp hs.2.1))
    simpa only [tr, selectedTrace, hb, ↓reduceIte, widthCount] using h

inductive SelectedPath (M : ℕ) : SAT.CNF (Fin n) → List Bool → SAT.CNF (Fin n) → Prop
  | nil (F : SAT.CNF (Fin n)) : SelectedPath M F [] F
  | step {F G : SAT.CNF (Fin n)} {p : List Bool} {c : ℕ} {H : SAT.Clause (Fin n)}
      (b : Bool) (hselect : SparsePriority.Priority F M c H)
      (tail : SelectedPath M (if b then childB F c H else childA F c H) p G) :
      SelectedPath M F (b :: p) G

theorem SelectedPath.trace_data {M : ℕ} {F G : SAT.CNF (Fin n)} {p : List Bool}
    (hp : SelectedPath M F p G) :
    ∃ (formulas : ℕ → SAT.CNF (Fin n)) (widths : ℕ → ℕ)
      (cores : ℕ → SAT.Clause (Fin n)), formulas 0 = F ∧
      (∀ t < p.length, SparsePriority.Priority (formulas t) M (widths t) (cores t)) ∧
      (∀ t < p.length, formulas (t + 1) = if p.getD t false then
        childB (formulas t) (widths t) (cores t) else
        childA (formulas t) (widths t) (cores t)) := by
  induction hp with
  | nil F =>
    exact ⟨fun _ => F, fun _ => 0, fun _ => ∅, rfl, by simp, by simp⟩
  | @step F G p c H b hs hp ih =>
    obtain ⟨f, w, s, hf, hselect, hnext⟩ := ih
    refine ⟨(fun | 0 => F | t + 1 => f t), (fun | 0 => c | t + 1 => w t),
      (fun | 0 => H | t + 1 => s t), rfl, ?_, ?_⟩
    · intro t ht
      cases t with
      | zero => exact hs
      | succ t => exact hselect t (by simpa using ht)
    · intro t ht
      cases t with
      | zero => simpa using hf
      | succ t => simpa using hnext t (by simpa using ht)

theorem SelectedPath.length_le {M k : ℕ} {F G : SAT.CNF (Fin n)} {p : List Bool}
    (hp : SelectedPath M F p G) (hM : 2 ≤ M)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k F) :
    p.length ≤ depthConstant k M * n := by
  obtain ⟨f, w, s, hf, hs, hn⟩ := hp.trace_data
  apply selected_path_depth_le f w s (fun t => p.getD t false) M k hM hs hn
  · simpa only [hf] using hanti
  · simpa only [hf] using hnt
  · simpa only [hf] using hwidth

theorem SelectedPath.count_true_mul_le {M k : ℕ} {F G : SAT.CNF (Fin n)} {p : List Bool}
    (hp : SelectedPath M F p G) (hM : 2 ≤ M)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : SAT.WidthAtMost k F) :
    p.count true * M ≤ rightConstant k * n := by
  have hpositions : ((Finset.range p.length).filter fun t => p.getD t false = true) =
      BranchTree.bPositions p := by
    ext t
    simp [BranchTree.bPositions, Option.getD_eq_iff]
  obtain ⟨f, w, s, hf, hs, hn⟩ := hp.trace_data
  rw [← BranchTree.card_bPositions_eq_count, ← hpositions]
  apply selected_path_right_steps_mul_le f w s (fun t => p.getD t false) M k hM hs hn
  · simpa only [hf] using hanti
  · simpa only [hf] using hnt
  · simpa only [hf] using hwidth

end SelectedTrace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCharging
