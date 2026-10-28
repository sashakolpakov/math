import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafInput
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun

/-! The leaf's serialized raw clauses and the selector's indexed clauses
have exactly the same ambient models. Repeated clauses or literals are not
assigned extra model multiplicity. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics

open SqrtLog DisjointReuse
open scoped BigOperators

/-- Index the actual list of clauses without renaming any ambient variable. -/
def indexed {n : ℕ} (F : RawCNF n) (i : Fin F.length) : SAT.Clause (Fin n) :=
  ExecCNF.clauseSet (F.get i)

/-- Literal codes for each actual serialized clause, without sorting or
removing raw occurrences. The dependent index cast changes only its proof. -/
def recordIndex {n : ℕ} (F : RawCNF n) (i : Fin (NativeTerminal.clauseRecords F).length) :
    Fin F.length := ⟨i.val, by simpa [NativeTerminal.clauseRecords] using i.isLt⟩

def recordCodes {n : ℕ} (F : RawCNF n) (i : Fin (NativeTerminal.clauseRecords F).length) :
    List ℕ := (F.get (recordIndex F i)).map Encoding.literalCode

theorem recordCodes_word {n : ℕ} (F : RawCNF n)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    (NativeTerminal.clauseRecords F)[i.val] =
      Encoding.encodeList Encoding.encodeNat (recordCodes F i) := by
  simp only [NativeTerminal.clauseRecords, List.getElem_map, recordCodes,
    List.get_eq_getElem, recordIndex, ExecSparsifyEncoding.encodeList_map]
  rfl

theorem recordCodes_lt {n : ℕ} (F : RawCNF n)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    ∀ v ∈ recordCodes F i, v < 2 * n := by
  intro v hv
  obtain ⟨lit,_hmem,rfl⟩ := List.mem_map.mp hv
  exact Encoding.literalCode_lt lit

theorem recordCodes_length {n k : ℕ} (F : RawCNF n)
    (hv : DisjointReuse.SparseDFSRefinement.Valid k F)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    (recordCodes F i).length ≤ k := by
  simp only [recordCodes, List.length_map]
  exact hv.width _ (List.get_mem F (recordIndex F i))

/-- Indexing the original list gives its semantic clause set, including when
that list contains repeated clauses or repeated literals. -/
theorem indexed_image {n : ℕ} (F : RawCNF n) :
    Finset.univ.image (indexed F) = ExecCNF.formulaSet F := by
  ext C
  simp only [Finset.mem_image, Finset.mem_univ, true_and, ExecCNF.mem_formulaSet]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨F.get i, List.get_mem F i, hi⟩
  · rintro ⟨D,hD,hC⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hD
    exact ⟨i,hC⟩

theorem indexed_eval {n : ℕ} (F : RawCNF n) (x : SAT.Assignment (Fin n)) :
    (∀ i, (indexed F i).eval x = true) ↔ SAT.CNF.eval x (ExecCNF.formulaSet F) = true := by
  rw [← indexed_image F]
  simp

theorem indexed_count {n : ℕ} (F : RawCNF n) :
    SAT.count (Finset.univ.image (indexed F)) = rawCount F := by
  rw [indexed_image]
  rfl

/-- The sum ranges over all assignments on the declared Fin n, including
coordinates unused by every clause. -/
theorem rawCount_sum {n : ℕ} (F : RawCNF n) :
    rawCount F = ∑ x : SAT.Assignment (Fin n),
      if ∀ i, (indexed F i).eval x = true then 1 else 0 := by
  unfold rawCount SAT.count SAT.satisfyingAssignments
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [(indexed_eval F x).symm]

/-- The exact greedily selected history accepts precisely the original raw
formula, using the good code matrices produced by native preparation. -/
theorem history_accepts {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (HashGreedyCNF.rowAccept (indexed F))
      (HashGreedyCNF.history (indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) x = true ↔
      SAT.CNF.eval x (ExecCNF.formulaSet F) = true :=
  (HashGreedyCode.supplied_history_accepts_iff (indexed F) hm hB shifts Q hs hQ x).trans
    (indexed_eval F x)

/-- This is the full unmarked accepted count, not the violation mass or a
single marked query's count. -/
theorem history_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1)) :
    HashSelect.acceptedCount (HashGreedyCNF.rowAccept (indexed F))
      (HashGreedyCNF.history (indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) = rawCount F := by
  rw [HashGreedyCode.supplied_history_count_eq (indexed F) hm hB shifts Q hs hQ]
  exact (rawCount_sum F).symm

theorem history_count_word {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1)) :
    countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (indexed F))
      (HashGreedyCNF.history (indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length))) = countWord (rawCount F) :=
  congrArg countWord (history_count F hm hB shifts Q hs hQ)

/-- Read the actual selected-history boundary supplied by the native rounds.
The last count query must still execute on this history to produce the word. -/
theorem native_history_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (base out : StructuredProgram.State 40 896)
    (hout : HashGreedyRound.RowBoundary base
      (HashGreedyCNF.history (indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) out) :
    ∃ rows : List (List Bool), out.stacks 777 = HashGreedyProgram.encodedHistory rows ∧
      HashSelect.acceptedCount (HashGreedyCNF.rowAccept (indexed F)) rows = rawCount F ∧
      (0 < HashSelect.acceptedCount (HashGreedyCNF.rowAccept (indexed F)) rows ↔
        SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨rows, hr, _hmass, hc, hp⟩ := HashGreedyRun.exit_exact_models (indexed F) hm
    (HashGreedyCode.initial shifts Q) base out
    (HashGreedyCode.initial_code_distance hm hB shifts Q hs hQ) hout
  rw [indexed_image] at hc hp
  exact ⟨rows,hr,hc,hp⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
