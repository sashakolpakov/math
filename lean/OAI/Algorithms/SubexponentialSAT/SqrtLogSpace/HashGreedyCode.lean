import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramRawTable

/-! Actual supplied-code row payloads initialize the streamed selector. Raw
slot bounds retain repeated indices and zero coefficients, as the physical
assembler does; they do not substitute semantic support for retained data. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

abbrev initial {m B : ℕ} (shifts : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) : List (List Bool) :=
  LeafScopeResourceBounds.initialPayloads (HashCandidates.digitWidth m)
    (CodeRowsProgram.serializedRows m shifts Q)

abbrev raw (m : ℕ) (hm : 0 < m) :=
  LeafScopeResourceBounds.rawDecode m (HashCandidates.digitWidth m) hm

/-- Exact bytes at the serializer-to-history port; no unpaid reversal. -/
theorem initial_encoding {m B : ℕ} (shifts : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) :
    HashGreedyProgram.encodedHistory (initial shifts Q) =
      CodeRowsProgram.rowStream (HashCandidates.digitWidth m) m shifts Q := by
  unfold initial LeafScopeResourceBounds.initialPayloads CodeRowsProgram.rowStream
    HashGreedyProgram.encodedHistory
  induction CodeRowsProgram.serializedRows m shifts Q with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, List.reverse_reverse, Encoding.encodeList]
    simpa only [List.map_map, id_eq] using congrArg
      (fun tail => true :: (Encoding.frame (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m row) ++ tail)) ih

theorem initial_raw {m B : ℕ} (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) :
    (initial shifts Q).map (raw m hm) = CodeRowsProgram.serializedRows m shifts Q :=
  LeafScopeResourceBounds.initialPayloads_decode hm (HashCandidates.digitWidth_sufficient m) _

theorem initial_code_distance {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) shifts)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1))
    (v : HashSelect.Row m)
    (hv : ∀ r ∈ (initial shifts Q).map (decode m), (∑ e, r e * v e) = 0)
    (hv0 : v ≠ 0) : m ≤ SparseCode.distanceDenom m B * SparseCode.weight v :=
  LeafOuterProgram.initial_kernel_bound hm hB (HashCandidates.digitWidth_sufficient m)
    shifts Q hs hQ v hv hv0

/-- Goodness and distance are properties of the actually returned candidates;
no identity with the old chosenGraph/chosenLocal definitions is required. -/
theorem supplied_history_count_eq {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) shifts)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1)) :
    HashSelect.acceptedCount (rowAccept clauses)
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) (HashSelect.loopCap n m)) =
        ∑ x : SAT.Assignment (Fin n), if ∀ e, (clauses e).eval x = true then 1 else 0 :=
  history_count_eq clauses hm _ _ (initial_code_distance hm hB shifts Q hs hQ)

theorem supplied_history_accepts_iff {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) shifts)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1))
    (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (rowAccept clauses)
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) (HashSelect.loopCap n m)) x = true ↔
        ∀ e, (clauses e).eval x = true :=
  history_accepts_iff clauses hm _ _ (initial_code_distance hm hB shifts Q hs hQ) x

/-- Satisfiability follows from positivity of the whole exact accepted count. -/
theorem supplied_history_positive_iff {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) shifts)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1)) :
    0 < HashSelect.acceptedCount (rowAccept clauses)
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) (HashSelect.loopCap n m)) ↔
        ∃ x : SAT.Assignment (Fin n), ∀ e, (clauses e).eval x = true := by
  rw [HashSelect.acceptedCount_pos_iff]
  exact exists_congr (supplied_history_accepts_iff clauses hm hB shifts Q hs hQ)

/-- A normalized candidate always decodes to exactly depth raw occurrences. -/
theorem candidate_raw_length {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    (raw m hm (HashGreedyCandidate.candidate m depth rank)).length = depth :=
  LeafScopeResourceBounds.rawDecode_generated_length hm (HashCandidates.digitWidth_sufficient m)
    _ (HashGreedyCandidate.candidate_mem hm depth rank)

theorem chosen_raw_length {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (rows : List (List Bool)) :
    (raw m hm (HashGreedyRound.chosenEntry (entry clauses depth)
      (HashCandidates.payloadWidth m depth) rows).payload).length = depth := by
  obtain ⟨rank, _, he⟩ := HashGreedyRound.chosenEntry_mem (entry clauses depth)
    (HashCandidates.payloadWidth m depth) rows
  rw [he]
  exact candidate_raw_length hm depth rank

/-- Raw slots are retained even when their finite-field contribution cancels. -/
theorem history_raw_slots {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth : ℕ) (start : List (List Bool)) (rounds : ℕ) :
    LeafScopeResourceBounds.slots ((history clauses depth start rounds).map (raw m hm)) =
      LeafScopeResourceBounds.slots (start.map (raw m hm)) + rounds * depth := by
  induction rounds with
  | zero => simp [history, HashSelectProgram.iter]
  | succ rounds ih =>
    unfold history at *
    rw [HashSelectProgram.iter_succ_apply, HashGreedyRound.nextRows]
    simp only [List.map_cons, LeafScopeResourceBounds.slots, List.sum_cons]
    simp only [LeafScopeResourceBounds.slots] at ih
    rw [chosen_raw_length clauses hm, ih]
    ring

theorem history_raw_rows {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (depth D : ℕ) (start : List (List Bool))
    (hstart : ∀ bits ∈ start, (raw m hm bits).length ≤ D) (rounds : ℕ) :
    ∀ row ∈ (history clauses depth start rounds).map (raw m hm), row.length ≤ D + depth + 1 := by
  induction rounds with
  | zero =>
    intro row hrow
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hrow
    have h := hstart bits hb
    exact h.trans (by omega)
  | succ rounds ih =>
    intro row hrow
    unfold history at hrow
    rw [HashSelectProgram.iter_succ_apply, HashGreedyRound.nextRows, List.map_cons] at hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · rw [chosen_raw_length clauses hm]
      omega
    · exact ih row hrow

/-- Selected histories retain the actual initial rows and exactly one raw
row per completed round, without adding the current losing trial. -/
theorem supplied_history_raw_resources {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds : ℕ) :
    let rows := (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    rows.length = SparseCode.totalRows m B + rounds ∧
      LeafScopeResourceBounds.slots rows ≤
        SparseCode.totalRows m B * SparseCode.degreeBound m B + rounds * SparseCode.distanceDenom m B ∧
      ∀ row ∈ rows, row.length ≤ SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1 := by
  dsimp only
  have hi : ∀ bits ∈ initial shifts Q, (raw m hm bits).length ≤ SparseCode.degreeBound m B := by
    intro bits hb
    apply CodeRowsProgram.serializedRows_supplied_slots shifts Q
    rw [← initial_raw hm shifts Q]
    exact List.mem_map.mpr ⟨bits, hb, rfl⟩
  have hlen : (initial shifts Q).length = SparseCode.totalRows m B := by
    simp [initial, LeafScopeResourceBounds.initialPayloads,
      CodeRowsProgram.serializedRows_supplied_length]
  refine ⟨?_, ?_, history_raw_rows clauses hm _ _ _ hi rounds⟩
  · simp [history, HashGreedyRound.iter_length, hlen]
  · rw [history_raw_slots, initial_raw hm shifts Q]
    exact Nat.add_le_add_right (LeafScopeResourceBounds.supplied_slots shifts Q) _

/-- This applies to the final unmarked exact-count query with mark=none and
rounds=loopCap, as well as every attained prefix. Raw repeats and zeros remain
charged before the physical scope producer removes duplicate variables. -/
theorem supplied_history_scope_resources {n B : ℕ} (wireClauses : List (List Bool))
    (clauses : Fin wireClauses.length → SAT.Clause (Fin n)) (hm : 0 < wireClauses.length)
    (shifts : SparseCode.SuppliedShifts wireClauses.length B)
    (Q : SparseCode.SuppliedLocal wireClauses.length B)
    (t d k rounds : ℕ) (codes : Fin wireClauses.length → List ℕ)
    (hcodes : ∀ i, (codes i).length ≤ k) (mark : Option (Fin wireClauses.length)) :
    let m := wireClauses.length
    let rows := (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
    scopes.length ≤ SparseCode.totalRows m B + rounds + 1 ∧
      LeafScopeResourceBounds.slots scopes ≤
        (SparseCode.totalRows m B * SparseCode.degreeBound m B +
          rounds * SparseCode.distanceDenom m B + 1) * k ∧
      ∀ row ∈ scopes, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k := by
  dsimp only
  obtain ⟨hlength, hslots, hrows⟩ := supplied_history_raw_resources clauses hm shifts Q rounds
  have hmark : mark.isSome.toNat ≤ 1 := by cases mark <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [HashScopeProgram.Complete.scopes_length, hlength]
    omega
  · apply (LeafScopeResourceBounds.scope_mass t d k codes hcodes _ mark).trans
    apply Nat.mul_le_mul_right k
    omega
  · exact LeafScopeResourceBounds.scope_arity t d k _ codes hcodes _ mark hrows (by omega)

/-- All trials, including losers, have bounded physical raw-row resources. -/
theorem supplied_trial_raw_resources {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (rounds rank : ℕ) :
    let rows := (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    rows.length = SparseCode.totalRows m B + rounds + 1 ∧
      LeafScopeResourceBounds.slots rows ≤
        SparseCode.totalRows m B * SparseCode.degreeBound m B +
          (rounds + 1) * SparseCode.distanceDenom m B ∧
      ∀ row ∈ rows, row.length ≤ SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1 := by
  dsimp only
  have hi : ∀ bits ∈ initial shifts Q, (raw m hm bits).length ≤ SparseCode.degreeBound m B := by
    intro bits hb
    apply CodeRowsProgram.serializedRows_supplied_slots shifts Q
    rw [← initial_raw hm shifts Q]
    exact List.mem_map.mpr ⟨bits, hb, rfl⟩
  have hlen : (initial shifts Q).length = SparseCode.totalRows m B := by
    simp [initial, LeafScopeResourceBounds.initialPayloads,
      CodeRowsProgram.serializedRows_supplied_length]
  refine ⟨?_, ?_, ?_⟩
  · simp [history, HashGreedyRound.iter_length, hlen, Nat.add_assoc]
  · have hh := history_raw_slots clauses hm (SparseCode.distanceDenom m B) (initial shifts Q) rounds
    rw [initial_raw hm shifts Q] at hh
    have hs := LeafScopeResourceBounds.supplied_slots shifts Q
    simp only [List.map_cons, LeafScopeResourceBounds.slots, List.sum_cons]
    simp only [LeafScopeResourceBounds.slots] at hh
    rw [candidate_raw_length, hh]
    nlinarith
  · intro row hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · rw [candidate_raw_length]
      omega
    · exact history_raw_rows clauses hm _ _ _ hi rounds row hrow

/-- Physical scope generation charges every raw occurrence and the optional
marked clause. This bound does not discard zero or repeated tuple entries. -/
theorem supplied_trial_scope_resources {n B : ℕ} (wireClauses : List (List Bool))
    (clauses : Fin wireClauses.length → SAT.Clause (Fin n)) (hm : 0 < wireClauses.length)
    (shifts : SparseCode.SuppliedShifts wireClauses.length B)
    (Q : SparseCode.SuppliedLocal wireClauses.length B)
    (t d k rounds rank : ℕ) (codes : Fin wireClauses.length → List ℕ)
    (hcodes : ∀ i, (codes i).length ≤ k) (mark : Option (Fin wireClauses.length)) :
    let m := wireClauses.length
    let rows := (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
    scopes.length ≤ SparseCode.totalRows m B + rounds + 2 ∧
      LeafScopeResourceBounds.slots scopes ≤
        (SparseCode.totalRows m B * SparseCode.degreeBound m B +
          (rounds + 1) * SparseCode.distanceDenom m B + 1) * k ∧
      ∀ row ∈ scopes, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k := by
  dsimp only
  obtain ⟨hlength, hslots, hrows⟩ := supplied_trial_raw_resources clauses hm shifts Q rounds rank
  have hmark : mark.isSome.toNat ≤ 1 := by cases mark <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [HashScopeProgram.Complete.scopes_length, hlength]
    omega
  · apply (LeafScopeResourceBounds.scope_mass t d k codes hcodes _ mark).trans
    apply Nat.mul_le_mul_right k
    omega
  · exact LeafScopeResourceBounds.scope_arity t d k _ codes hcodes _ mark hrows (by omega)

/-- Semantic support is bounded by the same physical slot budget. -/
theorem initial_support_le {m B : ℕ} (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) :
    HashSelect.totalCost (supportCost m) (initial shifts Q) ≤
      SparseCode.totalRows m B * SparseCode.degreeBound m B := by
  have h : ∀ rows : List (List Bool), HashSelect.totalCost (supportCost m) rows ≤
      LeafScopeResourceBounds.slots (rows.map (raw m hm)) := by
    intro rows
    induction rows with
    | nil => simp [HashSelect.totalCost]
    | cons payload rows ih =>
      have hp : supportCost m payload ≤ (raw m hm payload).length := by
        rw [LeafScopeResourceBounds.rawDecode_length]
        exact HashFamilyPayload.decoded_rowSupport_le _ _ _ _
      simpa only [HashSelect.totalCost_cons, List.map_cons, LeafScopeResourceBounds.slots,
        List.sum_cons] using Nat.add_le_add hp ih
  exact (h _).trans (by rw [initial_raw hm shifts Q]; exact LeafScopeResourceBounds.supplied_slots shifts Q)

/-- Re-encoding a normalized streamed candidate recovers its literal stored
payload, including all zero and repeated raw slots. -/
theorem candidate_raw_payload {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m
      (raw m hm (HashGreedyCandidate.candidate m depth rank))).reverse =
        HashGreedyCandidate.candidate m depth rank :=
  LeafScopeResourceBounds.rawDecode_generated_payload hm
    (HashCandidates.digitWidth_sufficient m) _ (HashGreedyCandidate.candidate_mem hm depth rank)

/-- Every actual selected history payload has an exact raw-row decoding.
Selection membership comes from the concrete streamed minimum proof. -/
theorem supplied_history_raw_payloads {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds : ℕ) :
    ∀ p ∈ history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds,
      (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m (raw m hm p)).reverse = p := by
  induction rounds with
  | zero =>
    intro p hp
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hp
    unfold raw
    rw [LeafScopeResourceBounds.rawDecode_rowPayload hm (HashCandidates.digitWidth_sufficient m)]
  | succ rounds ih =>
    intro p hp
    unfold history at hp
    rw [HashSelectProgram.iter_succ_apply, HashGreedyRound.nextRows] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨rank, _, he⟩ := HashGreedyRound.chosenEntry_mem
        (entry clauses (SparseCode.distanceDenom m B))
        (HashCandidates.payloadWidth m (SparseCode.distanceDenom m B))
        (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)
      unfold history at he
      rw [he]
      exact candidate_raw_payload hm _ rank
    · exact ih p hp

/-- This is byte equality between the existing history stream and the raw
scope-stage input. It does not perform an uncharged reversal or conversion. -/
theorem raw_encoding {m : ℕ} (hm : 0 < m) (rows : List (List Bool))
    (hrows : ∀ p ∈ rows,
      (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m (raw m hm p)).reverse = p) :
    HashGreedyProgram.encodedHistory rows =
      HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m) (rows.map (raw m hm)) := by
  unfold HashGreedyProgram.encodedHistory HashScopeProgram.RawTable.inputBits
  apply congrArg (Encoding.encodeList id)
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  have h := congrArg List.reverse (hrows p hp)
  have hbits : HashScopeProgram.RawTable.rowBits (HashCandidates.digitWidth m) (raw m hm p) =
      CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m (raw m hm p) := rfl
  rw [Function.comp_apply, hbits]
  simpa only [List.reverse_reverse] using h.symm

/-- Actual777 accepted-history bytes are exactly the final query's raw rows. -/
theorem supplied_history_raw_encoding {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds : ℕ) :
    HashGreedyProgram.encodedHistory
      (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds) =
    HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m)
      ((history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)) :=
  raw_encoding hm _ (supplied_history_raw_payloads clauses hm shifts Q rounds)

/-- The actual staged candidate prefix and777 tail equal the literal raw
trial table for every rank, including losing candidates. -/
theorem supplied_trial_raw_encoding {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) (rounds rank : ℕ) :
    true :: (Encoding.frame (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank).reverse ++
      HashGreedyProgram.encodedHistory
        (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)) =
    HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m)
      ((HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
        history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)) := by
  have h := raw_encoding hm
    (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds) (by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact candidate_raw_payload hm _ rank
        · exact supplied_history_raw_payloads clauses hm shifts Q rounds p hp)
  simpa only [HashGreedyProgram.encodedHistory, List.map_cons, Encoding.encodeList, id_eq]
    using h

/-- The binary odometer's actual current word selects exactly the same raw
trial table; leading zero bits and the parser's reversal are accounted for. -/
theorem supplied_trial_word_raw_encoding {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (rounds : ℕ) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m (SparseCode.distanceDenom m B)) :
    true :: (Encoding.frame
      (HashCandidates.normalize m (SparseCode.distanceDenom m B) word.reverse).reverse ++
      HashGreedyProgram.encodedHistory
        (history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds)) =
    HashScopeProgram.RawTable.inputBits (HashCandidates.digitWidth m)
      ((HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) (CounterPrograms.value word) ::
        history clauses (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)) := by
  rw [← HashGreedyCandidate.candidate_at_word word hword]
  exact supplied_trial_raw_encoding clauses hm shifts Q rounds _

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
