import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowPrepare
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowsFrame
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisCoveredRow

namespace OAI.Algorithms

/-! The enclosing metadata branch and cleanup for physical basis rows. -/

namespace SubexponentialSAT.Subexp.GlobalBasisRowPrepare

open BitProgram StructuredCalls

def rowLow : Fin 32 → Fin 64 := Fin.castAdd 32

/-- Every row starts with empty private work. The matrix accumulator on12,
constants on13--15, and all retained high inputs lie outside this predicate. -/
def RowClean (d : Data) : Prop :=
  ∀ i : Fin 64, i.val < 12 ∨ (16 ≤ i.val ∧ i.val ≤ 31) ∨
    i.val = 36 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 → d.stacks i = []

def rowCleared (port : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩

theorem clear_eval (port : Fin 64) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (rowCleared port d) :=
  .call _ (ListRegisterProgram.clear_run port 0 1 d.regs d.stacks)

theorem metadata_input (records : List (List Bool × List Bool)) (query : List Bool)
    (d : Data) (h33 : d.stacks 33 = SelectorProgram.rawRecords records)
    (h34 : d.stacks 34 = query) (hc : RowClean d) :
    projectState metadataRegs metadataPorts d =
      GlobalBasisMetadata.inputState (d.regs ∘ metadataRegs)
        (SelectorProgram.rawRecords records) query := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i
  · exact h33
  · exact h34
  all_goals exact hc _ (by decide)

theorem leftover_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (rank : ℕ) (d : Data)
    (hfind : records.lookup query = some
      (GlobalBasisMetadata.Metadata.leftover (List.replicate rank true)).encode)
    (h33 : d.stacks 33 = SelectorProgram.rawRecords records)
    (h34 : d.stacks 34 = query) (hc : RowClean d) :
    ∃ n e, n ≤ 400 * (GlobalBasisMetadata.volume records query)^2 + 4 ∧
      Eval command n d e ∧
      e.stacks = Function.update d.stacks 5 (List.replicate rank true) ∧ e.regs 6 = false := by
  obtain ⟨n, a, hn, ha, hsa, hra⟩ := metadata_eval records query
    (.leftover (List.replicate rank true)) d hfind (metadata_input records query d h33 h34 hc)
  have h3 : d.stacks 3 = [] := hc 3 (by decide)
  have h36 : d.stacks 36 = [] := hc 36 (by decide)
  have ha36 : a.stacks 36 = [] := by simp [hsa, GlobalBasisMetadata.Metadata.typeCode]
  have hbranch : Eval (.ite 6 covered (.base .skip)) 1 a a :=
    .ite_false hra (.base (.skip _))
  have he := ha.seq (hbranch.seq (clear_eval 36 a))
  refine ⟨n + (1 + (2 * (a.stacks 36).length + 3)), rowCleared 36 a, ?_, he, ?_, ?_⟩
  · rw [ha36]
    simp only [List.length_nil]
    omega
  · funext i
    by_cases hi3 : i = 3 <;> by_cases hi36 : i = 36 <;> by_cases hi5 : i = 5 <;>
      simp_all [rowCleared, GlobalBasisMetadata.Metadata.block,
        GlobalBasisMetadata.Metadata.typeCode, GlobalBasisMetadata.Metadata.rank]
  · simpa [rowCleared, readRegs, GlobalBasisMetadata.Metadata.coveredFlag] using hra

def leftoverRow (p rank : ℕ) : GlobalBasisEntry.Row p where
  N := 0
  table := fun i => Fin.elim0 i
  coordinate := 0
  block := 0
  color := 0
  rank := rank
  covered := false

theorem leftover_ready {p : ℕ} [Fact p.Prime] (rank : ℕ) (d e : Data)
    (hc : RowClean d)
    (h13 : d.stacks 13 = List.replicate (GlobalBasisEntry.frameWidth p) true)
    (h14 : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0)
    (h15 : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1)
    (hs : e.stacks = Function.update d.stacks 5 (List.replicate rank true))
    (hr : e.regs 6 = false) :
    GlobalBasisRows.Invariant (leftoverRow p rank) (projectState id rowLow e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · have h0 := hc 0 (by decide)
      simpa [projectState, rowLow, hs, leftoverRow, BasisTransposeProgram.rows] using h0
    · simpa [projectState, rowLow, hs, leftoverRow, GlobalBasisEntryCore.unary] using hc 1 (by decide)
    · simpa [projectState, rowLow, hs, leftoverRow, GlobalBasisEntryCore.unary] using hc 2 (by decide)
    · simpa [projectState, rowLow, hs, leftoverRow, GlobalBasisEntryCore.unary] using hc 3 (by decide)
    · simpa [projectState, rowLow, hs, leftoverRow, GlobalBasisEntryCore.unary] using hc 4 (by decide)
    · simp [projectState, rowLow, hs, leftoverRow, GlobalBasisEntryCore.unary]
    · simpa [projectState, rowLow, hs, leftoverRow, GlobalBasisEntryCore.unary] using h13
    · simpa [projectState, rowLow, hs] using h14
    · simpa [projectState, rowLow, hs] using h15
    · simpa [projectState, leftoverRow] using hr
    · simpa [projectState, rowLow, hs] using hc 11 (by decide)
    · intro i hi
      have hi5 : rowLow i ≠ 5 := by
        intro h
        have hh := congrArg Fin.val h
        change i.val = 5 at hh
        omega
      have hwork := hc (rowLow i) (Or.inr (Or.inl ⟨hi, by change i.val ≤ 31; omega⟩))
      simpa [projectState, hs, hi5] using hwork
  · simpa [projectState, rowLow, hs] using hc 8 (by decide)
  · simpa [projectState, rowLow, hs] using hc 9 (by decide)
  · simpa [projectState, rowLow, hs] using hc 10 (by decide)

def rowStacks {p : ℕ} [Fact p.Prime] (R : GlobalBasisEntry.Row p)
    (s : Fin 64 → List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s 0
      (BasisTransposeProgram.rows (MatrixWordEncoding.code p) R.table).flatten)
        1 (List.replicate R.N true)) 2 (List.replicate R.coordinate true))
          3 (List.replicate R.block true)) 4 (List.replicate R.color true))
            5 (List.replicate R.rank true)

theorem rowStacks_frame {p : ℕ} [Fact p.Prime] (R : GlobalBasisEntry.Row p)
    (s : Fin 64 → List Bool) (i : Fin 64) (hi : 6 ≤ i.val) :
    rowStacks R s i = s i := by
  have h0 : i ≠ 0 := by intro h; subst i; change 6 ≤ 0 at hi; omega
  have h1 : i ≠ 1 := by intro h; subst i; change 6 ≤ 1 at hi; omega
  have h2 : i ≠ 2 := by intro h; subst i; change 6 ≤ 2 at hi; omega
  have h3 : i ≠ 3 := by intro h; subst i; change 6 ≤ 3 at hi; omega
  have h4 : i ≠ 4 := by intro h; subst i; change 6 ≤ 4 at hi; omega
  have h5 : i ≠ 5 := by intro h; subst i; change 6 ≤ 5 at hi; omega
  simp [rowStacks, h0, h1, h2, h3, h4, h5]

theorem invariant_congr {p : ℕ} [Fact p.Prime] {R : GlobalBasisEntry.Row p}
    {a b : GlobalBasisRows.Data} (ha : GlobalBasisRows.Invariant R a)
    (hs : b.stacks = a.stacks) (hr : b.regs 6 = a.regs 6) :
    GlobalBasisRows.Invariant R b := by
  exact ⟨ha.1.congr hs hr, by simpa [hs] using ha.2.1,
    by simpa [hs] using ha.2.2.1, by simpa [hs] using ha.2.2.2⟩

theorem clear_type_ready {p : ℕ} [Fact p.Prime] {R : GlobalBasisEntry.Row p} {d : Data}
    (h : GlobalBasisCoveredRow.RowReady R d) :
    GlobalBasisCoveredRow.RowReady R (rowCleared 36 d) := by
  apply invariant_congr h
  · funext i
    have hi : GlobalBasisCoveredRow.lowPorts i ≠ 36 := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = 36 at hv
      omega
    simp [projectState, rowCleared, hi]
  · simp [projectState, rowCleared, readRegs]

def coveredBudget {r Q Δ : ℕ} (u : MulticolorTypes.UniversalType r Q Δ) (t : Fin Q)
    (N split : ℕ) (records : List (List Bool × List Bool)) (query batch : List Bool) : ℕ :=
  400 * (GlobalBasisMetadata.volume records query)^2 + 1 +
    GlobalBasisCoveredRow.budget u t N split batch +
    2 * (CollisionProgram.encodeType u).length + 3

/-- Metadata lookup supplies the actual branch flag and type word. The
covered-row services then derive the color, coordinate, and table from those
bytes. The original type buffer is physically cleared before returning. -/
theorem covered_eval {p r Q Δ : ℕ} [Fact p.Prime]
    (u : MulticolorTypes.UniversalType r Q Δ) (t : Fin Q)
    (records : List (List Bool × List Bool)) (query : List Bool)
    (before : List (List Bool)) (N split block : ℕ)
    (table : Fin N → Fin N → ZMod p) (tail : List Bool) (d : Data)
    (hfind : records.lookup query = some
      (GlobalBasisMetadata.Metadata.covered (List.replicate block true)
        (CollisionProgram.encodeType u)).encode)
    (h33 : d.stacks 33 = SelectorProgram.rawRecords records)
    (h34 : d.stacks 34 = query) (hc : RowClean d)
    (h32 : d.stacks 32 = List.replicate t.val true)
    (h37 : d.stacks 37 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ))
    (h38 : d.stacks 38 = List.replicate r true)
    (h40 : d.stacks 40 = GlobalBasisRecordLookup.recordsPrefix before ++
      GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload N split
        (BasisTransposeProgram.rows (MatrixWordEncoding.code p) table).flatten) ++ tail)
    (hindex : before.length = (u.head t).val)
    (h13 : d.stacks 13 = List.replicate (GlobalBasisEntry.frameWidth p) true)
    (h14 : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0)
    (h15 : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1)
    (hN : N = (GlobalBasisCoveredRow.sideWords u t).length) :
    ∃ n e, n ≤ coveredBudget u t N split records query (d.stacks 40) ∧
      Eval command n d e ∧
      e.stacks = rowStacks (GlobalBasisCoveredRow.row u t block N table) d.stacks ∧
      GlobalBasisCoveredRow.RowReady (GlobalBasisCoveredRow.row u t block N table) e := by
  obtain ⟨n, a, hn, ha, hsa, hra⟩ := metadata_eval records query
    (.covered (List.replicate block true) (CollisionProgram.encodeType u)) d hfind
      (metadata_input records query d h33 h34 hc)
  have hI : GlobalBasisCoveredRow.Input u t before N split
      (BasisTransposeProgram.rows (MatrixWordEncoding.code p) table).flatten tail a := by
    constructor
    · simp [hsa, GlobalBasisMetadata.Metadata.typeCode]
    · simpa [hsa] using h32
    · simpa [hsa] using h37
    · simpa [hsa] using h38
    · simpa [hsa] using h40
    · exact hindex
    · intro i hi
      simp only [GlobalBasisCoveredRow.workPorts, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [hsa] using hc _ (by decide)
  obtain ⟨m, b, hm, hb, hsb, hready, _⟩ := GlobalBasisCoveredRow.command_ready u t before
    N split block table tail a hI
    (by simp [hsa, GlobalBasisMetadata.Metadata.block])
    (by simp [hsa, GlobalBasisMetadata.Metadata.rank])
    (by simpa [hsa] using h13) (by simpa [hsa] using h14) (by simpa [hsa] using h15) hra hN
  have hb36 : b.stacks 36 = CollisionProgram.encodeType u := by
    simp [hsb, GlobalBasisCoveredRow.prepared, hsa, GlobalBasisMetadata.Metadata.typeCode]
  have hb40 : a.stacks 40 = d.stacks 40 := by simp [hsa]
  have hbranch : Eval (.ite 6 covered (.base .skip)) (m + 1) a b := .ite_true hra hb
  have he := ha.seq (hbranch.seq (clear_eval 36 b))
  refine ⟨n + (m + 1 + (2 * (b.stacks 36).length + 3)), rowCleared 36 b, ?_, he, ?_,
    clear_type_ready hready⟩
  · rw [hb40] at hm
    rw [hb36]
    unfold coveredBudget
    omega
  · have h36 := hc 36 (by decide)
    funext i
    fin_cases i <;>
      simp [rowCleared, hsb, GlobalBasisCoveredRow.prepared, hsa, rowStacks,
        GlobalBasisCoveredRow.row, GlobalBasisMetadata.Metadata.block,
        GlobalBasisMetadata.Metadata.typeCode, GlobalBasisMetadata.Metadata.rank,
        GlobalBasisCoveredRow.unary, h36]

theorem rowStacks_leftover {p : ℕ} [Fact p.Prime] (rank : ℕ) (d : Data) (hc : RowClean d) :
    rowStacks (leftoverRow p rank) d.stacks = Function.update d.stacks 5 (List.replicate rank true) := by
  funext i
  fin_cases i <;>
    simp [rowStacks, leftoverRow, BasisTransposeProgram.rows,
      hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide), hc 4 (by decide)]

theorem leftover_program_runsIn {p : ℕ} [Fact p.Prime]
    (records : List (List Bool × List Bool)) (query : List Bool) (rank : ℕ) (d : Data)
    (hfind : records.lookup query = some
      (GlobalBasisMetadata.Metadata.leftover (List.replicate rank true)).encode)
    (h33 : d.stacks 33 = SelectorProgram.rawRecords records)
    (h34 : d.stacks 34 = query) (hc : RowClean d)
    (h13 : d.stacks 13 = List.replicate (GlobalBasisEntry.frameWidth p) true)
    (h14 : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0)
    (h15 : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1) :
    ∃ e : Data, RunsIn program (400 * (GlobalBasisMetadata.volume records query)^2 + 5)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = rowStacks (leftoverRow p rank) d.stacks ∧
      GlobalBasisCoveredRow.RowReady (leftoverRow p rank) e := by
  obtain ⟨n, e, hn, he, hs, hr⟩ := leftover_eval records query rank d hfind h33 h34 hc
  refine ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 34 0⟩, ?_, ?_⟩
  · simpa only [rowStacks_leftover rank d hc] using hs
  · exact leftover_ready rank d e hc h13 h14 h15 hs hr

theorem covered_program_runsIn {p r Q Δ : ℕ} [Fact p.Prime]
    (u : MulticolorTypes.UniversalType r Q Δ) (t : Fin Q)
    (records : List (List Bool × List Bool)) (query : List Bool)
    (before : List (List Bool)) (N split block : ℕ)
    (table : Fin N → Fin N → ZMod p) (tail : List Bool) (d : Data)
    (hfind : records.lookup query = some
      (GlobalBasisMetadata.Metadata.covered (List.replicate block true)
        (CollisionProgram.encodeType u)).encode)
    (h33 : d.stacks 33 = SelectorProgram.rawRecords records)
    (h34 : d.stacks 34 = query) (hc : RowClean d)
    (h32 : d.stacks 32 = List.replicate t.val true)
    (h37 : d.stacks 37 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ))
    (h38 : d.stacks 38 = List.replicate r true)
    (h40 : d.stacks 40 = GlobalBasisRecordLookup.recordsPrefix before ++
      GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload N split
        (BasisTransposeProgram.rows (MatrixWordEncoding.code p) table).flatten) ++ tail)
    (hindex : before.length = (u.head t).val)
    (h13 : d.stacks 13 = List.replicate (GlobalBasisEntry.frameWidth p) true)
    (h14 : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0)
    (h15 : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1)
    (hN : N = (GlobalBasisCoveredRow.sideWords u t).length) :
    ∃ e : Data, RunsIn program (coveredBudget u t N split records query (d.stacks 40) + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = rowStacks (GlobalBasisCoveredRow.row u t block N table) d.stacks ∧
      GlobalBasisCoveredRow.RowReady (GlobalBasisCoveredRow.row u t block N table) e := by
  obtain ⟨n, e, hn, he, hs, hr⟩ := covered_eval u t records query before N split block table tail d
    hfind h33 h34 hc h32 h37 h38 h40 hindex h13 h14 h15 hN
  exact ⟨e, ⟨n+1, by omega, compiled_halt_trace he 34 0⟩, hs, hr⟩

end SubexponentialSAT.Subexp.GlobalBasisRowPrepare

end OAI.Algorithms
