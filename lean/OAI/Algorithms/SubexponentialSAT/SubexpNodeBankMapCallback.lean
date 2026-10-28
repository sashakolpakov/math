import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankMapSupport
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms

namespace OAI.Algorithms

/-! One actual matrix-record callback for the ordered point-bank mapper. -/

namespace SubexponentialSAT.SubexpNodeBankMap

open BitProgram StructuredCalls SubexpScanPrimitives Subexp

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

structure Matrix (p rows : ℕ) where
  columns : ℕ
  entries : Fin rows → Fin columns → ZMod p

def payload {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows) : List Bool :=
  Encoding.frame (List.replicate M.columns true) ++
    Encoding.frame (BlockCoefficientProgram.matrixBits p M.entries)

def bankList {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows) : List Bool :=
  ProgramEncoding.encodeRecords (MatrixImageEnumeration.bankRecords p M.entries)

def lowBase (p rows : ℕ) [Fact p.Prime] (i : Fin 32) : List Bool :=
  if i = 5 then MatrixWordEncoding.modulus p
  else if i = 14 then MatrixWordEncoding.zero p
  else if i = 17 then List.replicate rows true
  else if i = 18 then ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p)
  else []

def store (low : Fin 32 → List Bool) (regs : Fin 16 → Bool)
    (source parsed accum output : List Bool) (frame : Fin 24 → List Bool) : Data :=
  ⟨regs, fun i => Fin.addCases (m := 32) (n := 32) low
    (fun j => Fin.addCases (m := 8) (n := 24)
      ![source, parsed, accum, output, [], [], [], []] frame j) i⟩

def stored (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source parsed accum output : List Bool) (frame : Fin 24 → List Bool) : Data :=
  store (lowBase p rows) regs source parsed accum output frame

def ports : RecordPrograms.Ports 16 64 :=
  ⟨13, 14, 15, 32, 33, by decide, by decide, by decide, by decide⟩

def flags (regs : Fin 16 → Bool) (tag present found : Bool) : Fin 16 → Bool :=
  Function.update (Function.update (Function.update regs 13 tag) 14 present) 15 found

theorem parser_state (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source parsed accum output source' parsed' : List Bool)
    (frame : Fin 24 → List Bool) (tag present found : Bool) :
    RecordPrograms.state ports (stored p rows regs source parsed accum output frame)
      tag present found source' parsed' =
    stored p rows (flags regs tag present found) source' parsed' accum output frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem flags_eq_self (regs : Fin 16 → Bool) (tag present found : Bool)
    (ht : regs 13 = tag) (hp : regs 14 = present) (hf : regs 15 = found) :
    flags regs tag present found = regs := by
  funext i
  by_cases h13 : i = 13 <;> by_cases h14 : i = 14 <;> by_cases h15 : i = 15 <;>
    subst_vars <;> simp_all [flags]

def callback : Code :=
  .seq (transfer 33 37)
    (.seq (readWord 37 19 (by decide))
      (.seq (readWord 37 16 (by decide))
        (.seq enumerate
          (.seq (emitRecord 22 34 (by decide)) (.seq (clear 16) (clear 19))))))

def callbackCost {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows) : ℕ :=
  (3 * (payload M).length + 3) + (9 * M.columns + 7) +
    (9 * (BlockCoefficientProgram.matrixBits p M.entries).length + 7) +
    MatrixImageEnumeration.sourceBudget p M.entries + (8 * (bankList M).length + 10) +
    (2 * (BlockCoefficientProgram.matrixBits p M.entries).length + 3) + (2 * M.columns + 3)


def parsedData {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool) : Data :=
  let d0 := stored p rows regs tail (payload M).reverse accum output frame
  let d1 := afterTransfer d0 33 37 0 1
  let d2 := readResult d1 37 19 (List.replicate M.columns true)
    (Encoding.frame (BlockCoefficientProgram.matrixBits p M.entries))
  readResult d2 37 16 (BlockCoefficientProgram.matrixBits p M.entries) []

private theorem parsed_entry_0 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (i : Fin 8) :
    (parsedData M regs tail accum output frame).stacks (matrixStacks (Fin.castAdd 24 i)) =
      (MatrixImageEnumeration.stored p M.entries (fun _ => false) [] [] []).stacks (Fin.castAdd 24 i) := by
  fin_cases i <;>
    simp [parsedData, readResult, afterTransfer, StackRoutines.transferStacks,
      stored, store, lowBase, matrixStacks, MatrixImageEnumeration.stored]

private theorem parsed_entry_1 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (i : Fin 8) :
    (parsedData M regs tail accum output frame).stacks (matrixStacks (Fin.natAdd 8 (Fin.castAdd 16 i))) =
      (MatrixImageEnumeration.stored p M.entries (fun _ => false) [] [] []).stacks (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  fin_cases i <;>
    simp [parsedData, readResult, afterTransfer, StackRoutines.transferStacks,
      stored, store, lowBase, matrixStacks, MatrixImageEnumeration.stored]

private theorem parsed_entry_2 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (i : Fin 8) :
    (parsedData M regs tail accum output frame).stacks (matrixStacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i)))) =
      (MatrixImageEnumeration.stored p M.entries (fun _ => false) [] [] []).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))) := by
  fin_cases i <;>
    simp [parsedData, readResult, afterTransfer, StackRoutines.transferStacks,
      stored, store, lowBase, matrixStacks, MatrixImageEnumeration.stored]

private theorem parsed_entry_3 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (i : Fin 8) :
    (parsedData M regs tail accum output frame).stacks (matrixStacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i)))) =
      (MatrixImageEnumeration.stored p M.entries (fun _ => false) [] [] []).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))) := by
  fin_cases i <;>
    simp [parsedData, readResult, afterTransfer, StackRoutines.transferStacks,
      stored, store, lowBase, matrixStacks, MatrixImageEnumeration.stored]

theorem parsed_entry {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (i : Fin 32) :
    (parsedData M regs tail accum output frame).stacks (matrixStacks i) =
      (MatrixImageEnumeration.stored p M.entries (fun _ => false) [] [] []).stacks i := by
  refine Fin.addCases (m := 8) (n := 24) (fun j => ?_) (fun j => ?_) i
  · exact parsed_entry_0 M regs tail accum output frame j
  · refine Fin.addCases (m := 8) (n := 16) (fun k => ?_) (fun k => ?_) j
    · exact parsed_entry_1 M regs tail accum output frame k
    · refine Fin.addCases (m := 8) (n := 8) (fun l => ?_) (fun l => ?_) k
      · exact parsed_entry_2 M regs tail accum output frame l
      · exact parsed_entry_3 M regs tail accum output frame l

def finishData (e : Data) : Data := cleared (cleared (emitResult e 22 34) 16) 19

private theorem finish_stacks_0 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.castAdd 56 i) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.castAdd 56 i) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

private theorem finish_stacks_1 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.natAdd 8 (Fin.castAdd 48 i)) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.natAdd 8 (Fin.castAdd 48 i)) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

private theorem finish_stacks_2 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 40 i))) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 40 i))) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

private theorem finish_stacks_3 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 32 i)))) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 32 i)))) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

private theorem finish_stacks_4 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 24 i))))) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 24 i))))) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

private theorem finish_stacks_5 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 16 i)))))) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 16 i)))))) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

private theorem finish_stacks_6 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))))))) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))))))) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

private theorem finish_stacks_7 {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M))
    (i : Fin 8) :
    (finishData e).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))))))) =
      (stored p rows (finishData e).regs tail []
        (TupleProgram.prependRecord (bankList M) accum) output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))))))) := by
  fin_cases i <;>
    simp [finishData, cleared, emitResult, h, parsedData, readResult, afterTransfer,
      StackRoutines.transferStacks, stored, store, lowBase]

theorem finish_eq {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool)
    (e : Data)
    (h : e.stacks = Function.update (parsedData M regs tail accum output frame).stacks 22 (bankList M)) :
    finishData e = stored p rows (finishData e).regs tail []
      (TupleProgram.prependRecord (bankList M) accum) output frame := by
  apply state_ext
  · rfl
  · funext i
    refine Fin.addCases (m := 8) (n := 56) (fun a => ?_) (fun a => ?_) i
    · exact finish_stacks_0 M regs tail accum output frame e h a
    · refine Fin.addCases (m := 8) (n := 48) (fun b => ?_) (fun b => ?_) a
      · exact finish_stacks_1 M regs tail accum output frame e h b
      · refine Fin.addCases (m := 8) (n := 40) (fun c => ?_) (fun c => ?_) b
        · exact finish_stacks_2 M regs tail accum output frame e h c
        · refine Fin.addCases (m := 8) (n := 32) (fun d => ?_) (fun d => ?_) c
          · exact finish_stacks_3 M regs tail accum output frame e h d
          · refine Fin.addCases (m := 8) (n := 24) (fun f => ?_) (fun f => ?_) d
            · exact finish_stacks_4 M regs tail accum output frame e h f
            · refine Fin.addCases (m := 8) (n := 16) (fun g => ?_) (fun g => ?_) f
              · exact finish_stacks_5 M regs tail accum output frame e h g
              · refine Fin.addCases (m := 8) (n := 8) (fun h' => ?_) (fun h' => ?_) g
                · exact finish_stacks_6 M regs tail accum output frame e h h'
                · exact finish_stacks_7 M regs tail accum output frame e h h'

theorem callback_eval {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (regs : Fin 16 → Bool) (tail accum output : List Bool) (frame : Fin 24 → List Bool) :
    ∃ t ≤ callbackCost M, ∃ rf,
      Eval callback t
        (stored p rows regs tail (payload M).reverse accum output frame)
        (stored p rows rf tail [] (Subexp.TupleProgram.prependRecord (bankList M) accum)
          output frame) ∧
      (∀ i : Fin 16, 13 ≤ i.val → rf i = regs i) := by
  let d0 := stored p rows regs tail (payload M).reverse accum output frame
  let d1 := afterTransfer d0 33 37 0 1
  let d2 := readResult d1 37 19 (List.replicate M.columns true)
    (Encoding.frame (BlockCoefficientProgram.matrixBits p M.entries))
  let d3 := readResult d2 37 16 (BlockCoefficientProgram.matrixBits p M.entries) []
  have h1 : Eval (transfer 33 37) (3 * (payload M).length + 3) d0 d1 := by
    have hl : (d0.stacks 33).length = (payload M).length := by simp [d0, stored, store]
    simpa only [hl] using transfer_eval d0 33 37 (by decide)
  have h2 : Eval (readWord 37 19 (by decide)) (9 * M.columns + 7) d1 d2 := by
    have h := readWord_eval d1 37 19 (by decide) (by decide) (by decide)
      (List.replicate M.columns true) (Encoding.frame (BlockCoefficientProgram.matrixBits p M.entries))
      (by simp [d1, d0, afterTransfer, StackRoutines.transferStacks, stored, store, payload])
      (by simp [d1, d0, afterTransfer, StackRoutines.transferStacks, stored, store, lowBase])
      (by simp [d1, d0, afterTransfer, StackRoutines.transferStacks, stored, store])
    simpa only [List.length_replicate] using h
  have h3 : Eval (readWord 37 16 (by decide))
      (9 * (BlockCoefficientProgram.matrixBits p M.entries).length + 7) d2 d3 := by
    apply readWord_eval d2 37 16 (by decide) (by decide) (by decide)
    · simp [d2, readResult]
    · simp [d2, d1, d0, readResult, afterTransfer, StackRoutines.transferStacks,
        stored, store, lowBase]
    · simp [d2, d1, d0, readResult, afterTransfer, StackRoutines.transferStacks,
        stored, store]
  have hentry : ∀ i, d3.stacks (matrixStacks i) =
      (MatrixImageEnumeration.stored p M.entries (d3.regs ∘ matrixRegs) [] [] []).stacks i := by
    intro i
    exact parsed_entry M regs tail accum output frame i
  obtain ⟨tm, htm, e, hm, hregs, hstacks⟩ := enumerate_eval p M.entries d3 hentry
  let d4 := emitResult e 22 34
  let d5 := cleared d4 16
  let d6 := cleared d5 19
  have h4 : Eval (emitRecord 22 34 (by decide)) (8 * (bankList M).length + 10) e d4 := by
    have h := emitRecord_eval e 22 34 (by decide) (by decide) (by decide) (by
      rw [hstacks]
      simp [d3, d2, d1, d0, readResult, afterTransfer, StackRoutines.transferStacks,
        stored, store])
    simpa [hstacks, bankList] using h
  have h5 : Eval (clear 16)
      (2 * (BlockCoefficientProgram.matrixBits p M.entries).length + 3) d4 d5 := by
    have hl : (d4.stacks 16).length = (BlockCoefficientProgram.matrixBits p M.entries).length := by
      simp [d4, emitResult, hstacks, d3, readResult]
    simpa only [hl] using clear_eval d4 16
  have h6 : Eval (clear 19) (2 * M.columns + 3) d5 d6 := by
    have hl : (d5.stacks 19).length = M.columns := by
      simp [d5, cleared, d4, emitResult, hstacks, d3, d2, readResult]
    simpa only [hl] using clear_eval d5 19
  have hfinal : d6 = stored p rows d6.regs tail []
      (Subexp.TupleProgram.prependRecord (bankList M) accum) output frame := by
    exact finish_eq M regs tail accum output frame e hstacks
  have hh := h1.seq (h2.seq (h3.seq (hm.seq (h4.seq (h5.seq h6)))))
  rw [hfinal] at hh
  refine ⟨_, ?_, d6.regs, hh, ?_⟩
  · unfold callbackCost
    omega
  · intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    calc
      d6.regs i = e.regs i := by simp [d6, d5, d4, cleared, emitResult, readRegs, h0, h1]
      _ = d3.regs i := hregs i hi
      _ = regs i := by
        simp [d3, d2, d1, d0, readResult, afterTransfer, readRegs, h0, h1, stored, store]

end SubexponentialSAT.SubexpNodeBankMap

end OAI.Algorithms
