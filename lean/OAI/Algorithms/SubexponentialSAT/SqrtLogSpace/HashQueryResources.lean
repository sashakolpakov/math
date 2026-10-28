import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryScopeBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendHighRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendSemantics

/-! Concrete scope resources of the actual serialized raw-formula query.
The dependent clause-index cast preserves every repeated or zero raw slot;
these results use no identity with the former materialized selector. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryResources

open SqrtLog HighFrontendSources HashGreedyCode
open DisjointReuse

@[simp] theorem recordRows_length {n : ℕ} (F : RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) :
    (recordRows F rows).length = rows.length := by simp [recordRows, castRows]

@[simp] theorem recordRows_slots {n : ℕ} (F : RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) :
    LeafScopeResourceBounds.slots (recordRows F rows) = LeafScopeResourceBounds.slots rows := by
  simp [LeafScopeResourceBounds.slots, recordRows, castRows, List.map_map, Function.comp_def]

theorem recordRows_arity {n : ℕ} (F : RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (D : ℕ)
    (hrows : ∀ row ∈ rows, row.length ≤ D) :
    ∀ row ∈ recordRows F rows, row.length ≤ D := by
  intro row hrow
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  simpa only [List.length_map] using hrows r hr

/-- The frontend's literal scopeRows has the resource bounds of the actual
raw rows and actual raw clause widths. The optional mark contributes at most
one clause; each produced variable scope is duplicate-free. -/
theorem rawQuery_resources {n k : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (rows : HashScopeProgram.RawTable.Rows F.length)
    (mark : Option (Fin F.length)) (index width modulus ambient : List Bool)
    (R M D : ℕ) (hR : rows.length ≤ R) (hM : LeafScopeResourceBounds.slots rows ≤ M)
    (hD : 1 ≤ D) (hrows : ∀ row ∈ rows, row.length ≤ D) :
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ R + 1 ∧ LeafScopeResourceBounds.slots q.scopeRows ≤ (M + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤ D * k) ∧ (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only [rawQueryFromRows, rawQuery, LeafQueryFrontend.Query.scopeRows]
  have hcodes := NativeLeafSemantics.recordCodes_length F hv
  have hmark : (recordMark F mark).isSome.toNat ≤ 1 := by cases mark <;> simp [recordMark]
  refine ⟨?_, ?_, ?_, LeafScopeResourceBounds.scopes_nodup 1 0 _ _ _⟩
  · rw [HashScopeProgram.Complete.scopes_length, recordRows_length]
    omega
  · apply (LeafScopeResourceBounds.scope_mass 1 0 k _ hcodes _ _).trans
    rw [recordRows_slots]
    exact Nat.mul_le_mul_right k (by omega)
  · exact LeafScopeResourceBounds.scope_arity 1 0 k D _ hcodes _ _
      (recordRows_arity F rows D hrows) hD

/-- Every attained selected history, including the final unmarked query,
uses the concrete query record and the exact indexed raw formula. -/
theorem history_resources {n k B : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (mark : Option (Fin F.length)) (index width modulus ambient : List Bool) :
    let m := F.length
    let rows := (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ SparseCode.totalRows m B + rounds + 1 ∧
      LeafScopeResourceBounds.slots q.scopeRows ≤
        (SparseCode.totalRows m B * SparseCode.degreeBound m B +
          rounds * SparseCode.distanceDenom m B + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) ∧
      (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only
  obtain ⟨hR, hM, hrows⟩ := supplied_history_raw_resources (NativeLeafSemantics.indexed F) hm shifts Q rounds
  exact rawQuery_resources F hv _ mark index width modulus ambient _ _ _ hR.le hM (by omega) hrows

/-- Every trial rank, including every losing candidate, uses the same bounds.
The candidate and all initial/selected row occurrences are retained. -/
theorem trial_resources {n k B : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds rank : ℕ) (mark : Option (Fin F.length)) (index width modulus ambient : List Bool) :
    let m := F.length
    let rows := (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom m B)
        (initial shifts Q) rounds).map (raw m hm)
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ SparseCode.totalRows m B + rounds + 2 ∧
      LeafScopeResourceBounds.slots q.scopeRows ≤
        (SparseCode.totalRows m B * SparseCode.degreeBound m B +
          (rounds + 1) * SparseCode.distanceDenom m B + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) ∧
      (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only
  obtain ⟨hR, hM, hrows⟩ := supplied_trial_raw_resources (NativeLeafSemantics.indexed F) hm shifts Q rounds rank
  have h := rawQuery_resources F hv _ mark index width modulus ambient _ _ _ hR.le hM (by omega) hrows
  simpa only [Nat.add_assoc] using h

/-- Exact guard-resource envelope for the actual final or intermediate
selected-history query. Positivity is used only for the produced-code row
bound; no guard, layout, or evaluator is supplied. -/
theorem history_uniform_resources {n k B : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (hn : 0 < n) (hm : 0 < F.length)
    (hB : 0 < B) (hmb : F.length ≤ n * B)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (hrounds : rounds ≤ HashSelect.loopCap n F.length)
    (mark : Option (Fin F.length)) (index width modulus ambient : List Bool) :
    let m := F.length
    let rows := (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n m + 2 ∧
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound m B +
          (HashSelect.loopCap n m + 1) * SparseCode.distanceDenom m B + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) ∧
      (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only
  obtain ⟨hr, hmss, har, hnd⟩ := history_resources F hv hm shifts Q rounds mark index width modulus ambient
  have htotal := SparseCode.totalRows_le hn hm hB hmb
  have hslots := Nat.mul_le_mul_right (SparseCode.degreeBound F.length B) htotal
  have hnew := Nat.mul_le_mul_right (SparseCode.distanceDenom F.length B)
    (show rounds ≤ HashSelect.loopCap n F.length + 1 by omega)
  exact ⟨by omega, hmss.trans (Nat.mul_le_mul_right k (by omega)), har, hnd⟩

/-- The same envelope includes every losing trial and optional marked clause.
It is precisely the three numeric inputs to the structural scan-guard proof. -/
theorem trial_uniform_resources {n k B : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (hn : 0 < n) (hm : 0 < F.length)
    (hB : 0 < B) (hmb : F.length ≤ n * B)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds rank : ℕ) (hrounds : rounds ≤ HashSelect.loopCap n F.length)
    (mark : Option (Fin F.length)) (index width modulus ambient : List Bool) :
    let m := F.length
    let rows := (HashGreedyCandidate.candidate m (SparseCode.distanceDenom m B) rank ::
      HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom m B)
        (initial shifts Q) rounds).map (raw m hm)
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n m + 2 ∧
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound m B +
          (HashSelect.loopCap n m + 1) * SparseCode.distanceDenom m B + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) ∧
      (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only
  obtain ⟨hr, hmss, har, hnd⟩ := trial_resources F hv hm shifts Q rounds rank mark index width modulus ambient
  have htotal := SparseCode.totalRows_le hn hm hB hmb
  have hslots := Nat.mul_le_mul_right (SparseCode.degreeBound F.length B) htotal
  have hnew := Nat.mul_le_mul_right (SparseCode.distanceDenom F.length B)
    (Nat.add_le_add_right hrounds 1)
  exact ⟨by omega, hmss.trans (Nat.mul_le_mul_right k (by omega)), har, hnd⟩

/-- The physical ambient and clause-count words identify the exact measured
input. The width word is a separate parameter and is not the clause count. -/
theorem input_eq_forward_measured (q : LeafQueryFrontend.Query) (k n : ℕ)
    (hm : BinaryArithmetic.toNat q.modulus = q.clauses.length)
    (hn : BinaryArithmetic.toNat q.ambient = n) :
    q.input k = CostAssembly.measuredParameterInput q.scopeRows
      (CostAssembly.forwardHighMask q.scopeRows n (Nat.sqrt (Asymptotic.L n) + 1))
      q.clauses.length k := by
  rw [q.input_eq_measured k hm]
  simp only [LeafQueryFrontend.Query.forward, LeafQueryFrontend.highMask, hn,
    EarlyThreshold.threshold, CostAssembly.forwardHighMask, HighIncidenceProgram.Prepare.mass]

/-- One cutoff is fixed before the actual query, its rows, optional mark,
and serialized numeric words. It requires only the proved raw scope bounds. -/
theorem scope_guard_cutoff (k qi : ℕ) :
    ∃ N : ℕ, ∀ (q : LeafQueryFrontend.Query) (n B : ℕ),
      N ≤ n → BinaryArithmetic.toNat q.ambient = n →
      BinaryArithmetic.toNat q.modulus = q.clauses.length →
      0 < q.clauses.length → q.clauses.length ≤ n * B → B ≤ Asymptotic.L n ^ qi →
      q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound q.clauses.length B +
          (HashSelect.loopCap n q.clauses.length + 1) *
            SparseCode.distanceDenom q.clauses.length B + 1) * k →
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound q.clauses.length B +
          SparseCode.distanceDenom q.clauses.length B + 1) * k) →
      (∀ row ∈ q.scopeRows, row.Nodup) → LeafParametersProgram.Guard (q.input k) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_raw_scope_guards k qi)
  refine ⟨N, ?_⟩
  intro q n B hn ha hm hc hmb hB hr hmass har hnd
  rw [input_eq_forward_measured q k n hm ha]
  exact (hN n hn q.scopeRows q.clauses.length B hc hmb hB hr hmass har hnd).1

/-- Every attained history query, with any optional mark including none,
passes the same actual frontend guard after a width-fixed cutoff. -/
theorem history_guard_cutoff (k qi : ℕ) :
    ∃ N : ℕ, ∀ (n B : ℕ) (F : RawCNF n)
      (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      N ≤ n → 0 < n → 0 < B → F.length ≤ n * B → B ≤ Asymptotic.L n ^ qi →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (mark : Option (Fin F.length)) (index width modulus ambient : List Bool),
      BinaryArithmetic.toNat modulus = F.length → BinaryArithmetic.toNat ambient = n →
      let rows := (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).map (raw F.length hm)
      LeafParametersProgram.Guard ((rawQueryFromRows F rows mark index width modulus ambient).input k) := by
  obtain ⟨N, hN⟩ := scope_guard_cutoff k qi
  refine ⟨N, ?_⟩
  intro n B F hv hm hn hnpos hB hmb hpoly shifts Q rounds hr mark index width modulus ambient hmod hamb
  obtain ⟨hrows, hmass, har, hnd⟩ := history_uniform_resources F hv hnpos hm hB hmb
    shifts Q rounds hr mark index width modulus ambient
  apply hN _ n B hn hamb
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hmod
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hm
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hmb
  · exact hpoly
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hrows
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hmass
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using har
  · exact hnd

/-- The cutoff also covers every losing candidate rank and every marked
clause on its literal candidate-plus-history query. -/
theorem trial_guard_cutoff (k qi : ℕ) :
    ∃ N : ℕ, ∀ (n B : ℕ) (F : RawCNF n)
      (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      N ≤ n → 0 < n → 0 < B → F.length ≤ n * B → B ≤ Asymptotic.L n ^ qi →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds rank : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (mark : Option (Fin F.length)) (index width modulus ambient : List Bool),
      BinaryArithmetic.toNat modulus = F.length → BinaryArithmetic.toNat ambient = n →
      let rows := (HashGreedyCandidate.candidate F.length (SparseCode.distanceDenom F.length B) rank ::
        HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).map (raw F.length hm)
      LeafParametersProgram.Guard ((rawQueryFromRows F rows mark index width modulus ambient).input k) := by
  obtain ⟨N, hN⟩ := scope_guard_cutoff k qi
  refine ⟨N, ?_⟩
  intro n B F hv hm hn hnpos hB hmb hpoly shifts Q rounds rank hr mark index width modulus ambient hmod hamb
  obtain ⟨hrows, hmass, har, hnd⟩ := trial_uniform_resources F hv hnpos hm hB hmb
    shifts Q rounds rank hr mark index width modulus ambient
  apply hN _ n B hn hamb
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hmod
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hm
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hmb
  · exact hpoly
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hrows
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using hmass
  · simpa [rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords] using har
  · exact hnd

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryResources
