import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

/-! The concrete streamed selector uses the original ternary row semantics.
Its exact scores and normalized reference coverage discharge the greedy
contraction hypotheses. These statements concern the deterministic history
refined by the native run; native query and resource closure remain separate. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF

open SqrtLog
open scoped BigOperators

noncomputable section

def decode (m : ℕ) : List Bool → HashSelect.Row m :=
  HashFamilyPayload.decodeVariableRow m (HashCandidates.digitWidth m)

def rowAccept {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (payload : List Bool) : SAT.Assignment (Fin n) → Bool :=
  HashSelect.cnfRowAccept clauses (decode m payload)

def entry {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n)) (depth : ℕ) :=
  HashGreedyCandidate.entry (rowAccept clauses) (HashInput.violationWeight clauses) n m depth

def history {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n)) (depth : ℕ)
    (initial : List (List Bool)) (rounds : ℕ) : List (List Bool) :=
  HashSelectProgram.iter
    (HashGreedyRound.nextRows (entry clauses depth) (HashCandidates.payloadWidth m depth))
    rounds initial

/-- Reference indices retain the original tuple multiplicities. -/
def reference {m depth c : ℕ} (hcount : (3 * m) ^ depth = c + 1)
    (i : Fin (c + 1)) : List Bool :=
  HashFamilyPayload.encode (HashCandidates.digitWidth m)
    (HashFamily.enumerate m depth (Fin.cast hcount.symm i))

theorem decode_reference {m depth c : ℕ} (hm : 0 < m)
    (hcount : (3 * m) ^ depth = c + 1) (i : Fin (c + 1)) :
    decode m (reference hcount i) = HashSelect.tupleFamily hcount i := by
  exact HashFamilyPayload.decodeVariableRow_encode hm
    (HashCandidates.digitWidth_sufficient m) _

theorem accepts_decode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (rowAccept clauses) rows x =
      HashSelect.accepts (HashSelect.cnfRowAccept clauses) (rows.map (decode m)) x := by
  simp [HashSelect.accepts, rowAccept, List.all_map, Function.comp_def]

theorem mass_decode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) :
    HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses) rows =
      HashSelect.mass (HashSelect.cnfRowAccept clauses) (HashInput.violationWeight clauses)
        (rows.map (decode m)) := by
  simp only [HashSelect.mass, accepts_decode]

theorem entry_value {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (depth : ℕ) (rows : List (List Bool)) (rank : ℕ) :
    BinaryArgmin.value (entry clauses depth rows rank) =
      HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses)
        ((entry clauses depth rows rank).payload :: rows) := by
  exact HashGreedyCandidate.entry_value _ _ n m depth rows rank
    (by simp [SAT.Assignment]) (fun x => by simpa using HashInput.violationWeight_le clauses x)

theorem reference_covered {n m depth c : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hcount : (3 * m) ^ depth = c + 1) (rows : List (List Bool)) (i : Fin (c + 1)) :
    ∃ rank < 2 ^ HashCandidates.payloadWidth m depth,
      (entry clauses depth rows rank).payload = reference hcount i :=
  HashGreedyCandidate.candidate_covers _

theorem initial_coverage {n m depth c : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (hcount : (3 * m) ^ depth = c + 1) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) :
    ∀ x, HashSelect.accepts (rowAccept clauses) initial x = true →
      0 < HashInput.violationWeight clauses x →
      3 * HashSelect.survivingCandidates (rowAccept clauses) (reference hcount) x ≤
        2 * (c + 1) := by
  intro x ha hw
  have h := HashSelect.initial_coverage_of_code clauses hm hcount
    (initial.map (decode m)) hcode x ((accepts_decode clauses initial x) ▸ ha) hw
  simpa only [HashSelect.survivingCandidates, rowAccept, decode_reference hm] using h

/-- The exact payload/score accessor removes evaluator and family-coverage
premises from the contraction theorem. The initial code distance is supplied
by the independently constructed sparse code. -/
theorem history_mass_zero {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) :
    HashSelect.mass (rowAccept clauses) (HashInput.violationWeight clauses)
      (history clauses depth initial (HashSelect.loopCap n m)) = 0 := by
  have hp : 0 < (3 * m) ^ depth := pow_pos (by omega) _
  have hc : (3 * m) ^ depth = ((3 * m) ^ depth - 1) + 1 := by omega
  apply HashGreedyRound.iter_mass_zero (rowAccept clauses)
    (HashInput.violationWeight clauses) (entry clauses depth)
    (HashCandidates.payloadWidth m depth) (reference hc) initial n m
  · simp [SAT.Assignment]
  · intro x
    simpa using HashInput.violationWeight_le clauses x
  · intro q _ j _
    exact entry_value clauses depth _ j
  · intro q _ i
    exact reference_covered clauses hc _ i
  · exact initial_coverage clauses hm hc initial hcode

theorem history_accepts_iff {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (rowAccept clauses)
      (history clauses depth initial (HashSelect.loopCap n m)) x = true ↔
        ∀ e, (clauses e).eval x = true := by
  rw [accepts_decode]
  apply HashSelect.cnf_mass_zero_iff
  rw [← mass_decode]
  exact history_mass_zero clauses hm depth initial hcode

/-- Exact accepted-assignment count over the ambient Fin n, without deleting
unused coordinates or taking a low binary bit. -/
theorem history_count_eq {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool))
    (hcode : ∀ v : HashSelect.Row m,
      (∀ r ∈ initial.map (decode m), (∑ e, r e * v e) = 0) → v ≠ 0 →
        m ≤ depth * SparseCode.weight v) :
    HashSelect.acceptedCount (rowAccept clauses)
      (history clauses depth initial (HashSelect.loopCap n m)) =
        ∑ x : SAT.Assignment (Fin n), if ∀ e, (clauses e).eval x = true then 1 else 0 := by
  unfold HashSelect.acceptedCount
  apply Finset.sum_congr rfl
  intro x _
  simp only [history_accepts_iff clauses hm depth initial hcode x]

def supportCost (m : ℕ) (payload : List Bool) : ℕ :=
  (HashInput.rowSupport (decode m payload)).card

theorem candidate_support_le {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    supportCost m (HashGreedyCandidate.candidate m depth rank) ≤ depth := by
  unfold supportCost decode
  rw [HashFamilyPayload.decodeVariableRow_generated hm
    (HashCandidates.digitWidth_sufficient m) _ (HashGreedyCandidate.candidate_mem hm depth rank)]
  exact HashFamilyPayload.decoded_rowSupport_le _ _ _ _

theorem chosen_support_le {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (rows : List (List Bool)) :
    supportCost m (HashGreedyRound.chosenEntry (entry clauses depth)
      (HashCandidates.payloadWidth m depth) rows).payload ≤ depth := by
  obtain ⟨rank, _, he⟩ := HashGreedyRound.chosenEntry_mem (entry clauses depth)
    (HashCandidates.payloadWidth m depth) rows
  rw [he]
  exact candidate_support_le hm depth rank

/-- Every selected history, including all intermediate rounds, retains at most
one depth-sized row per completed round. -/
theorem history_support_le {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool)) (rounds : ℕ) :
    HashSelect.totalCost (supportCost m) (history clauses depth initial rounds) ≤
      HashSelect.totalCost (supportCost m) initial + rounds * depth := by
  induction rounds with
  | zero => simp [history, HashSelectProgram.iter]
  | succ rounds ih =>
    unfold history at *
    rw [HashSelectProgram.iter_succ_apply, HashGreedyRound.nextRows, HashSelect.totalCost_cons]
    have h := chosen_support_le clauses hm depth
      (HashSelectProgram.iter (HashGreedyRound.nextRows (entry clauses depth)
        (HashCandidates.payloadWidth m depth)) rounds initial)
    calc
      _ ≤ depth + (HashSelect.totalCost (supportCost m) initial + rounds * depth) :=
        Nat.add_le_add h ih
      _ = _ := by ring

/-- Losing candidates satisfy the same trial support bound. -/
theorem trial_support_le {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool)) (rounds rank : ℕ) :
    HashSelect.totalCost (supportCost m)
      (HashGreedyCandidate.candidate m depth rank :: history clauses depth initial rounds) ≤
        HashSelect.totalCost (supportCost m) initial + (rounds + 1) * depth := by
  rw [HashSelect.totalCost_cons]
  have h := Nat.add_le_add (candidate_support_le hm depth rank)
    (history_support_le clauses hm depth initial rounds)
  exact h.trans_eq (by ring)

/-- The support estimate is directly usable on the decoded mathematical rows. -/
theorem decoded_history_support_le {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (initial : List (List Bool)) (rounds : ℕ) :
    HashSelect.totalCost (fun r => (HashInput.rowSupport r).card)
      ((history clauses depth initial rounds).map (decode m)) ≤
        HashSelect.totalCost (fun r => (HashInput.rowSupport r).card)
          (initial.map (decode m)) + rounds * depth := by
  simp only [HashSelect.totalCost, List.map_map, Function.comp_def]
  change (List.map (supportCost m) (history clauses depth initial rounds)).sum ≤
    (List.map (supportCost m) initial).sum + rounds * depth
  exact history_support_le clauses hm depth initial rounds

/-- Every marked query sees a trial whose variable-scope cost is charged,
including trials discarded by the minimum comparison. -/
theorem trial_scope_le {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth k : ℕ) (hwidth : ∀ e, (clauses e).card ≤ k)
    (initial : List (List Bool)) (rounds rank : ℕ) :
    HashSelect.totalCost (fun r => (HashInput.hashScope clauses r).card)
      ((HashGreedyCandidate.candidate m depth rank ::
        history clauses depth initial rounds).map (decode m)) ≤
      k * (HashSelect.totalCost (supportCost m) initial + (rounds + 1) * depth) := by
  have h := HashSelect.list_scope_cost_le clauses
    ((HashGreedyCandidate.candidate m depth rank ::
      history clauses depth initial rounds).map (decode m)) k hwidth
  apply h.trans
  apply Nat.mul_le_mul_left k
  simp only [HashSelect.totalCost, List.map_map, Function.comp_def]
  change (List.map (supportCost m)
    (HashGreedyCandidate.candidate m depth rank :: history clauses depth initial rounds)).sum ≤
      (List.map (supportCost m) initial).sum + (rounds + 1) * depth
  exact trial_support_le clauses hm depth initial rounds rank

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
