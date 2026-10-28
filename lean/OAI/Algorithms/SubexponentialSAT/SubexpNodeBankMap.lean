import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankMapCallback

namespace OAI.Algorithms

/-!
# Actual ordered map from matrix records to point-bank lists

The matrix bundle and common scalar words are runtime stack data. Every
matrix is parsed and passed to the fixed matrix-image program. A final
record reversal restores the original outer-then-color order.
-/

namespace SubexponentialSAT.SubexpNodeBankMap

open BitProgram StructuredCalls SubexpScanPrimitives Subexp

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def mappedAcc {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (accum : List Bool) : List Bool :=
  matrices.foldl (fun acc M => TupleProgram.prependRecord (bankList M) acc) accum

theorem mappedAcc_eq {p rows : ℕ} [Fact p.Prime]
    (matrices : List (Matrix p rows)) (accum : List (List Bool)) :
    mappedAcc matrices (ProgramEncoding.encodeRecords accum) =
      ProgramEncoding.encodeRecords ((matrices.map bankList).reverse ++ accum) := by
  unfold mappedAcc
  rw [← List.foldl_map (f := bankList) (g := fun acc bits => TupleProgram.prependRecord bits acc),
    TupleProgram.fold_prependRecord, TupleProgram.appendEncoded_encodeRecords]

theorem loop_eval {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (regs : Fin 16 → Bool) (accum output : List Bool) (frame : Fin 24 → List Bool) :
    ∃ t ≤ 1 + RecordMappedPrograms.budget payload callbackCost matrices, ∃ rf,
      Eval (RecordPrograms.loop ports callback) t
        (RecordMappedPrograms.afterTag ports payload
          (stored p rows regs [] [] accum output frame) matrices [])
        (stored p rows rf [] [] (mappedAcc matrices accum) output frame) ∧
      rf 13 = false ∧ rf 14 = true ∧ rf 15 = false := by
  induction matrices generalizing regs accum with
  | nil =>
      refine ⟨1, by simp [RecordMappedPrograms.budget], flags regs false true false, ?_, ?_⟩
      · simpa [RecordMappedPrograms.afterTag, parser_state, mappedAcc] using
          (Eval.while_false (test := ports.tag) (body := RecordPrograms.body ports callback)
            (a := stored p rows (flags regs false true false) [] [] accum output frame)
            (by simp [ports, stored, store, flags]))
      · simp [flags]
  | cons M matrices ih =>
      let base := stored p rows regs [] [] accum output frame
      let tail := Encoding.encodeList payload matrices
      let nextAccum := TupleProgram.prependRecord (bankList M) accum
      have hr : Eval (RecordPrograms.reader ports) (6 * (payload M).length + 4)
          (RecordMappedPrograms.afterTag ports payload base (M :: matrices) [])
          (stored p rows (flags regs false true false) tail (payload M).reverse accum output frame) := by
        simpa [RecordMappedPrograms.afterTag, base, tail, parser_state] using
          RecordPrograms.reader_eval ports base (payload M) tail [] true true false
      obtain ⟨tc, htc, rc, hc, hrc⟩ := callback_eval M
        (flags regs false true false) tail accum output frame
      have hc13 : rc 13 = false := (hrc 13 (by decide)).trans (by simp [flags])
      have hc14 : rc 14 = true := (hrc 14 (by decide)).trans (by simp [flags])
      have hc15 : rc 15 = false := (hrc 15 (by decide)).trans (by simp [flags])
      have hcf : flags rc false true false = rc := flags_eq_self rc _ _ _ hc13 hc14 hc15
      let next := stored p rows rc [] [] nextAccum output frame
      have hp : Eval (RecordPrograms.atom (.pop ports.source ports.tag ports.present)) 1
          (stored p rows rc tail [] nextAccum output frame)
          (RecordMappedPrograms.afterTag ports payload next matrices []) := by
        simpa only [next, tail, parser_state, hcf, List.append_nil] using
          RecordMappedPrograms.pop_list_eval ports payload next matrices [] false true
      have hb : Eval (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
          (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (stored p rows rc tail [] nextAccum output frame)
          (RecordMappedPrograms.afterTag ports payload next matrices []) := by
        exact Eval.ite_false (by simpa [ports, stored, store] using hc15) hp
      obtain ⟨tr, htr, rf, ht, hf⟩ := ih rc nextAccum
      have hguard : (RecordMappedPrograms.afterTag ports payload base (M :: matrices) []).regs
          ports.tag = true := by simp [RecordMappedPrograms.afterTag]
      have he := Eval.while_true hguard (hr.seq (hc.seq hb)) ht
      refine ⟨(6 * (payload M).length + 4 + (tc + 2)) + tr + 1, ?_, rf, ?_, hf⟩
      · simp only [RecordMappedPrograms.budget]
        omega
      · simpa only [RecordPrograms.loop, RecordPrograms.body, next, base,
          mappedAcc, List.foldl_cons, nextAccum] using he

def iterate : Code := RecordPrograms.iterate ports callback

theorem iterate_eval {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (regs : Fin 16 → Bool) (accum output : List Bool) (frame : Fin 24 → List Bool) :
    ∃ t ≤ 3 + RecordMappedPrograms.budget payload callbackCost matrices, ∃ rf,
      Eval iterate t
        (stored p rows regs (Encoding.encodeList payload matrices) [] accum output frame)
        (stored p rows rf [] [] (mappedAcc matrices accum) output frame) := by
  let base := stored p rows regs [] [] accum output frame
  have hself : flags regs (regs 13) (regs 14) (regs 15) = regs :=
    flags_eq_self regs _ _ _ rfl rfl rfl
  have hset := RecordPrograms.set_found_eval ports base (regs 13) (regs 14) (regs 15)
    false (Encoding.encodeList payload matrices) []
  have hpop := RecordMappedPrograms.pop_list_eval ports payload base matrices [] (regs 13) (regs 14)
  simp only [List.append_nil] at hpop
  obtain ⟨t, ht, rf, he, _⟩ := loop_eval matrices regs accum output frame
  have hh := hset.seq (hpop.seq he)
  refine ⟨1 + (1 + t), by omega, rf, ?_⟩
  simpa only [iterate, RecordPrograms.iterate, base, parser_state, hself,
    List.append_nil] using hh

def stage : Code := .seq (copy 40 5) (.seq (copy 41 14)
  (.seq (copy 42 18) (.seq (copy 43 17) (TupleProgram.pushConst 34 0 false))))

def cleanup : Code := .seq (clear 5) (.seq (clear 14) (.seq (clear 18) (clear 17)))

def reverseRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def reverseStacks : Fin 4 → Fin 64 := ![34, 36, 35, 33]

theorem reverseRegs_injective : Function.Injective reverseRegs := Fin.castAdd_injective _ _
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

def reverseRecords : Code := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram reverseRegs reverseStacks)

def command : Code := .seq stage (.seq iterate
  (.seq (TupleProgram.pushConst 35 0 false) (.seq reverseRecords cleanup)))

def program := compiled command 32 35

def common (p rows : ℕ) [Fact p.Prime] (frame : Fin 20 → List Bool) : Fin 24 → List Bool :=
  fun i => Fin.addCases (m := 4) (n := 20)
    ![MatrixWordEncoding.modulus p, MatrixWordEncoding.zero p,
      ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p), List.replicate rows true] frame i

def commonSize (p rows : ℕ) [Fact p.Prime] : ℕ :=
  (MatrixWordEncoding.modulus p).length + (MatrixWordEncoding.zero p).length +
    (ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p)).length + rows

def stageCost (p rows : ℕ) [Fact p.Prime] : ℕ := 7 * commonSize p rows + 22
def cleanupCost (p rows : ℕ) [Fact p.Prime] : ℕ := 2 * commonSize p rows + 12


def stageFinishData (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) : Data :=
  let d0 := store (fun _ => []) regs source [] [] [] (common p rows frame)
  let d1 := afterCopy d0 40 5 0 1
  let d2 := afterCopy d1 41 14 0 1
  let d3 := afterCopy d2 42 18 0 1
  TupleProgram.pushedState 34 0 false (afterCopy d3 43 17 0 1)

private theorem stage_finish_0 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.castAdd 56 i) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.castAdd 56 i) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

private theorem stage_finish_1 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.natAdd 8 (Fin.castAdd 48 i)) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.natAdd 8 (Fin.castAdd 48 i)) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

private theorem stage_finish_2 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 40 i))) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 40 i))) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

private theorem stage_finish_3 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 32 i)))) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 32 i)))) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

private theorem stage_finish_4 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 24 i))))) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 24 i))))) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

private theorem stage_finish_5 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 16 i)))))) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 16 i)))))) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

private theorem stage_finish_6 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))))))) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))))))) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

private theorem stage_finish_7 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) (i : Fin 8) :
    (stageFinishData p rows regs source frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))))))) =
      (stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame)).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))))))) := by
  fin_cases i <;>
    simp [stageFinishData, TupleProgram.pushedState, afterCopy, StackRoutines.copyStacks,
      stored, store, common, lowBase, ProgramEncoding.encodeRecords, Encoding.encodeList]

theorem stage_finish_eq (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) :
    stageFinishData p rows regs source frame =
      stored p rows (stageFinishData p rows regs source frame).regs source []
        (ProgramEncoding.encodeRecords []) [] (common p rows frame) := by
  apply state_ext
  · rfl
  · funext i
    refine Fin.addCases (m := 8) (n := 56) (fun a => ?_) (fun a => ?_) i
    · exact stage_finish_0 p rows regs source frame a
    · refine Fin.addCases (m := 8) (n := 48) (fun b => ?_) (fun b => ?_) a
      · exact stage_finish_1 p rows regs source frame b
      · refine Fin.addCases (m := 8) (n := 40) (fun c => ?_) (fun c => ?_) b
        · exact stage_finish_2 p rows regs source frame c
        · refine Fin.addCases (m := 8) (n := 32) (fun d => ?_) (fun d => ?_) c
          · exact stage_finish_3 p rows regs source frame d
          · refine Fin.addCases (m := 8) (n := 24) (fun f => ?_) (fun f => ?_) d
            · exact stage_finish_4 p rows regs source frame f
            · refine Fin.addCases (m := 8) (n := 16) (fun g => ?_) (fun g => ?_) f
              · exact stage_finish_5 p rows regs source frame g
              · refine Fin.addCases (m := 8) (n := 8) (fun h => ?_) (fun h => ?_) g
                · exact stage_finish_6 p rows regs source frame h
                · exact stage_finish_7 p rows regs source frame h

def cleanupFinishData (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) : Data :=
  let d0 := stored p rows regs [] [] accum output frame
  cleared (cleared (cleared (cleared d0 5) 14) 18) 17

private theorem cleanup_finish_0 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.castAdd 56 i) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.castAdd 56 i) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

private theorem cleanup_finish_1 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.natAdd 8 (Fin.castAdd 48 i)) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.natAdd 8 (Fin.castAdd 48 i)) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

private theorem cleanup_finish_2 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 40 i))) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 40 i))) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

private theorem cleanup_finish_3 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 32 i)))) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 32 i)))) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

private theorem cleanup_finish_4 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 24 i))))) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 24 i))))) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

private theorem cleanup_finish_5 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 16 i)))))) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 16 i)))))) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

private theorem cleanup_finish_6 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))))))) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))))))) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

private theorem cleanup_finish_7 (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) (i : Fin 8) :
    (cleanupFinishData p rows regs accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))))))) =
      (store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))))))) := by
  fin_cases i <;>
    simp [cleanupFinishData, cleared, stored, store, lowBase]

theorem cleanup_finish_eq (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) :
    cleanupFinishData p rows regs accum output frame =
      store (fun _ => []) (cleanupFinishData p rows regs accum output frame).regs
        [] [] accum output frame := by
  apply state_ext
  · rfl
  · funext i
    refine Fin.addCases (m := 8) (n := 56) (fun a => ?_) (fun a => ?_) i
    · exact cleanup_finish_0 p rows regs accum output frame a
    · refine Fin.addCases (m := 8) (n := 48) (fun b => ?_) (fun b => ?_) a
      · exact cleanup_finish_1 p rows regs accum output frame b
      · refine Fin.addCases (m := 8) (n := 40) (fun c => ?_) (fun c => ?_) b
        · exact cleanup_finish_2 p rows regs accum output frame c
        · refine Fin.addCases (m := 8) (n := 32) (fun d => ?_) (fun d => ?_) c
          · exact cleanup_finish_3 p rows regs accum output frame d
          · refine Fin.addCases (m := 8) (n := 24) (fun f => ?_) (fun f => ?_) d
            · exact cleanup_finish_4 p rows regs accum output frame f
            · refine Fin.addCases (m := 8) (n := 16) (fun g => ?_) (fun g => ?_) f
              · exact cleanup_finish_5 p rows regs accum output frame g
              · refine Fin.addCases (m := 8) (n := 8) (fun h => ?_) (fun h => ?_) g
                · exact cleanup_finish_6 p rows regs accum output frame h
                · exact cleanup_finish_7 p rows regs accum output frame h


theorem stage_eval (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (source : List Bool) (frame : Fin 20 → List Bool) :
    ∃ rf, Eval stage (stageCost p rows)
      (store (fun _ => []) regs source [] [] [] (common p rows frame))
      (stored p rows rf source [] (ProgramEncoding.encodeRecords []) [] (common p rows frame)) := by
  let d0 := store (fun _ => []) regs source [] [] [] (common p rows frame)
  let d1 := afterCopy d0 40 5 0 1
  let d2 := afterCopy d1 41 14 0 1
  let d3 := afterCopy d2 42 18 0 1
  let d4 := afterCopy d3 43 17 0 1
  let d5 := TupleProgram.pushedState 34 0 false d4
  have h1 : Eval (copy 40 5) (7 * (MatrixWordEncoding.modulus p).length + 5) d0 d1 := by
    have hl : (d0.stacks 40).length = (MatrixWordEncoding.modulus p).length := by
      simp [d0, store, common]
    simpa only [hl] using copy_eval d0 40 5 (by decide) (by decide) (by decide)
      (by simp [d0, store])
  have h2 : Eval (copy 41 14) (7 * (MatrixWordEncoding.zero p).length + 5) d1 d2 := by
    have hl : (d1.stacks 41).length = (MatrixWordEncoding.zero p).length := by
      simp [d1, d0, afterCopy, StackRoutines.copyStacks, store, common]
    simpa only [hl] using
      copy_eval d1 41 14 (by decide) (by decide) (by decide)
        (by simp [d1, d0, afterCopy, StackRoutines.copyStacks, store])
  have h3 : Eval (copy 42 18)
      (7 * (ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p)).length + 5) d2 d3 := by
    have hl : (d2.stacks 42).length =
        (ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p)).length := by
      simp [d2, d1, d0, afterCopy, StackRoutines.copyStacks, store, common]
    simpa only [hl] using
      copy_eval d2 42 18 (by decide) (by decide) (by decide)
        (by simp [d2, d1, d0, afterCopy, StackRoutines.copyStacks, store])
  have h4 : Eval (copy 43 17) (7 * rows + 5) d3 d4 := by
    have hl : (d3.stacks 43).length = rows := by
      simp [d3, d2, d1, d0, afterCopy, StackRoutines.copyStacks, store, common]
    simpa only [hl] using
      copy_eval d3 43 17 (by decide) (by decide) (by decide)
        (by simp [d3, d2, d1, d0, afterCopy, StackRoutines.copyStacks, store])
  have h5 := TupleProgram.pushConst_eval 34 (0 : Fin 16) false d4
  have hend : d5 = stored p rows d5.regs source [] (ProgramEncoding.encodeRecords []) []
      (common p rows frame) := by
    exact stage_finish_eq p rows regs source frame
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  change Eval stage _ d0 d5 at he
  rw [hend] at he
  refine ⟨d5.regs, ?_⟩
  convert he using 1
  unfold stageCost commonSize
  omega

theorem cleanup_eval (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum output : List Bool) (frame : Fin 24 → List Bool) :
    ∃ rf, Eval cleanup (cleanupCost p rows)
      (stored p rows regs [] [] accum output frame)
      (store (fun _ => []) rf [] [] accum output frame) := by
  let d0 := stored p rows regs [] [] accum output frame
  let d1 := cleared d0 5
  let d2 := cleared d1 14
  let d3 := cleared d2 18
  let d4 := cleared d3 17
  have h1 : Eval (clear 5) (2 * (MatrixWordEncoding.modulus p).length + 3) d0 d1 := by
    have hl : (d0.stacks 5).length = (MatrixWordEncoding.modulus p).length := by
      simp [d0, stored, store, lowBase]
    simpa only [hl] using clear_eval d0 5
  have h2 : Eval (clear 14) (2 * (MatrixWordEncoding.zero p).length + 3) d1 d2 := by
    have hl : (d1.stacks 14).length = (MatrixWordEncoding.zero p).length := by
      simp [d1, d0, cleared, stored, store, lowBase]
    simpa only [hl] using clear_eval d1 14
  have h3 : Eval (clear 18)
      (2 * (ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p)).length + 3) d2 d3 := by
    have hl : (d2.stacks 18).length =
        (ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p)).length := by
      simp [d2, d1, d0, cleared, stored, store, lowBase]
    simpa only [hl] using clear_eval d2 18
  have h4 : Eval (clear 17) (2 * rows + 3) d3 d4 := by
    have hl : (d3.stacks 17).length = rows := by
      simp [d3, d2, d1, d0, cleared, stored, store, lowBase]
    simpa only [hl] using clear_eval d3 17
  have hend : d4 = store (fun _ => []) d4.regs [] [] accum output frame := by
    exact cleanup_finish_eq p rows regs accum output frame
  have he := h1.seq (h2.seq (h3.seq h4))
  change Eval cleanup _ d0 d4 at he
  rw [hend] at he
  refine ⟨d4.regs, ?_⟩
  convert he using 1
  unfold cleanupCost commonSize
  omega


theorem store_update_accum (low : Fin 32 → List Bool) (regs : Fin 16 → Bool)
    (source parsed accum output : List Bool) (frame : Fin 24 → List Bool) (bits : List Bool) :
    Function.update (store low regs source parsed accum output frame).stacks 34 bits =
      (store low regs source parsed bits output frame).stacks := by
  funext i
  refine Fin.addCases (m := 32) (n := 32) (fun j => ?_) (fun j => ?_) i
  · have hj : Fin.castAdd 32 j ≠ (34 : Fin 64) := by
      intro heq
      have hv := congrArg (fun q : Fin 64 => q.val) heq
      change j.val = 34 at hv
      have := j.isLt
      omega
    rw [Function.update_of_ne hj]
    simp only [store, Fin.addCases_left]
  · refine Fin.addCases (m := 8) (n := 24) (fun k => ?_) (fun k => ?_) j
    · fin_cases k <;> simp [store]
    · have hk : Fin.natAdd 32 (Fin.natAdd 8 k) ≠ (34 : Fin 64) := by
        intro heq
        have hv := congrArg (fun q : Fin 64 => q.val) heq
        change 32 + (8 + k.val) = 34 at hv
        omega
      rw [Function.update_of_ne hk]
      simp only [store, Fin.addCases_right]

theorem store_update_output (low : Fin 32 → List Bool) (regs : Fin 16 → Bool)
    (source parsed accum output : List Bool) (frame : Fin 24 → List Bool) (bits : List Bool) :
    Function.update (store low regs source parsed accum output frame).stacks 35 bits =
      (store low regs source parsed accum bits frame).stacks := by
  funext i
  refine Fin.addCases (m := 32) (n := 32) (fun j => ?_) (fun j => ?_) i
  · have hj : Fin.castAdd 32 j ≠ (35 : Fin 64) := by
      intro heq
      have hv := congrArg (fun q : Fin 64 => q.val) heq
      change j.val = 35 at hv
      have := j.isLt
      omega
    rw [Function.update_of_ne hj]
    simp only [store, Fin.addCases_left]
  · refine Fin.addCases (m := 8) (n := 24) (fun k => ?_) (fun k => ?_) j
    · fin_cases k <;> simp [store]
    · have hk : Fin.natAdd 32 (Fin.natAdd 8 k) ≠ (35 : Fin 64) := by
        intro heq
        have hv := congrArg (fun q : Fin 64 => q.val) heq
        change 32 + (8 + k.val) = 35 at hv
        omega
      rw [Function.update_of_ne hk]
      simp only [store, Fin.addCases_right]

theorem stored_accum_output_frame (p rows : ℕ) [Fact p.Prime]
    (regs rf : Fin 16 → Bool) (accum output accum' output' : List Bool)
    (frame : Fin 24 → List Bool) (i : Fin 64) (h34 : i ≠ 34) (h35 : i ≠ 35) :
    (stored p rows rf [] [] accum' output' frame).stacks i =
      (stored p rows regs [] [] accum output frame).stacks i := by
  calc
    _ = (Function.update (Function.update
        (stored p rows regs [] [] accum output frame).stacks 34 accum') 35 output') i := by
      unfold stored
      rw [store_update_accum, store_update_output]
      rfl
    _ = _ := by simp [h34, h35]

theorem pushOutput_eq (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (accum : List Bool) (frame : Fin 24 → List Bool) :
    TupleProgram.pushedState 35 0 false (stored p rows regs [] [] accum [] frame) =
      stored p rows (Function.update regs 0 false) [] [] accum
        (ProgramEncoding.encodeRecords []) frame := by
  apply state_ext
  · rfl
  · exact store_update_output (lowBase p rows) regs [] [] accum [] frame [false]

theorem reverseRecords_eval (p rows : ℕ) [Fact p.Prime] (regs : Fin 16 → Bool)
    (records : List (List Bool)) (frame : Fin 24 → List Bool) :
    ∃ t ≤ 10 * (ProgramEncoding.encodeRecords records).length, ∃ rf,
      Eval reverseRecords t
        (stored p rows regs [] [] (ProgramEncoding.encodeRecords records)
          (ProgramEncoding.encodeRecords []) frame)
        (stored p rows rf [] [] [] (ProgramEncoding.encodeRecords records.reverse) frame) := by
  let d := stored p rows regs [] [] (ProgramEncoding.encodeRecords records)
    (ProgramEncoding.encodeRecords []) frame
  let a := SubexpNormalizeProgram.filterState (regs 0) (regs 1) (regs 2)
    (ProgramEncoding.encodeRecords records) [] (ProgramEncoding.encodeRecords []) []
  let b := SubexpNormalizeProgram.filterState false true false [] []
    (ProgramEncoding.encodeRecords records.reverse) []
  let rf := Function.extend reverseRegs b.regs regs
  obtain ⟨t, ht, he⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] []
    (regs 0) (regs 1) (regs 2)
  simp only [List.append_nil] at he
  change Trace SubexpNormalizeProgram.reverseRecordsProgram t
    (a.withPC (some SubexpNormalizeProgram.reverseRecordsProgram.entry)) (b.withPC none) at he
  have hin : embedState reverseRegs reverseStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ reverseRegs_injective reverseStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [d, a, reverseStacks, stored, store,
        SubexpNormalizeProgram.filterState]
    · intros; rfl
  have hout : embedState reverseRegs reverseStacks d b =
      stored p rows rf [] [] [] (ProgramEncoding.encodeRecords records.reverse) frame := by
    apply embedState_eq_of_ports _ _ _ _ _ reverseRegs_injective reverseStacks_injective
    · intro i
      exact reverseRegs_injective.extend_apply _ _ i
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [b, reverseStacks, stored, store,
        SubexpNormalizeProgram.filterState]
    · intro i hi
      have h34 : i ≠ 34 := fun h => hi ⟨0, by simpa [reverseStacks] using h.symm⟩
      have h35 : i ≠ 35 := fun h => hi ⟨2, by simpa [reverseStacks] using h.symm⟩
      exact stored_accum_output_frame p rows regs rf _ _ _ _ frame i h34 h35
  have hh := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegs reverseStacks d reverseRegs_injective reverseStacks_injective he
  rw [hin, hout] at hh
  exact ⟨t, ht, rf, hh⟩

def runtimeBound {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows)) : ℕ :=
  stageCost p rows + (3 + RecordMappedPrograms.budget payload callbackCost matrices) +
    2 + 10 * (ProgramEncoding.encodeRecords ((matrices.map bankList).reverse)).length +
    cleanupCost p rows + 1

def input {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool) : Data :=
  store (fun _ => []) regs (Encoding.encodeList payload matrices) [] [] [] (common p rows frame)

def result {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool) : Data :=
  store (fun _ => []) regs [] [] []
    (ProgramEncoding.encodeRecords (matrices.map bankList)) (common p rows frame)

theorem input_source {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool) :
    (input matrices regs frame).stacks 32 =
      ProgramEncoding.encodeRecords (matrices.map payload) := by
  change Encoding.encodeList payload matrices = _
  induction matrices with
  | nil => rfl
  | cons M matrices ih =>
      simpa only [Encoding.encodeList, List.map_cons, ProgramEncoding.encodeRecords, id_eq] using
        congrArg (fun tail => true :: (Encoding.frame (payload M) ++ tail)) ih

theorem command_eval {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool) :
    ∃ t, t + 1 ≤ runtimeBound matrices ∧ ∃ rf,
      Eval command t (input matrices regs frame) (result matrices rf frame) := by
  obtain ⟨r1, h1⟩ := stage_eval p rows regs (Encoding.encodeList payload matrices) frame
  obtain ⟨ti, hti, r2, h2⟩ := iterate_eval matrices r1 (ProgramEncoding.encodeRecords []) []
    (common p rows frame)
  rw [mappedAcc_eq, List.append_nil] at h2
  let middle := stored p rows r2 [] []
    (ProgramEncoding.encodeRecords ((matrices.map bankList).reverse)) [] (common p rows frame)
  have h3 := TupleProgram.pushConst_eval 35 (0 : Fin 16) false middle
  have hmiddle : TupleProgram.pushedState 35 0 false middle =
      stored p rows (Function.update r2 0 false) [] []
        (ProgramEncoding.encodeRecords ((matrices.map bankList).reverse))
        (ProgramEncoding.encodeRecords []) (common p rows frame) := by
    exact pushOutput_eq p rows r2 _ _
  rw [hmiddle] at h3
  obtain ⟨tr, htr, r4, h4⟩ := reverseRecords_eval p rows (Function.update r2 0 false)
    (matrices.map bankList).reverse (common p rows frame)
  simp only [List.reverse_reverse] at h4
  obtain ⟨rf, h5⟩ := cleanup_eval p rows r4 []
    (ProgramEncoding.encodeRecords (matrices.map bankList)) (common p rows frame)
  refine ⟨_, ?_, rf, h1.seq (h2.seq (h3.seq (h4.seq h5)))⟩
  unfold runtimeBound
  omega

/-- The complete finite program, including its final halt, creates the bank
bundle in exactly the order of the supplied matrix records. -/
theorem program_run {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool) :
    ∃ rf, RunsIn program (runtimeBound matrices)
      ((input matrices regs frame).withPC (some program.entry))
      ((result matrices rf frame).withPC none) := by
  obtain ⟨t, ht, rf, he⟩ := command_eval matrices regs frame
  exact ⟨rf, t + 1, ht, compiled_halt_trace he 32 35⟩

@[simp] theorem result_output {p rows : ℕ} [Fact p.Prime]
    (matrices : List (Matrix p rows)) (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool) :
    (result matrices regs frame).stacks 35 =
      ProgramEncoding.encodeRecords (matrices.map bankList) := rfl

theorem result_frame {p rows : ℕ} [Fact p.Prime]
    (matrices : List (Matrix p rows)) (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool)
    (i : Fin 20) :
    (result matrices regs frame).stacks (Fin.natAdd 44 i) = frame i := by
  have hi : Fin.natAdd 44 i = Fin.natAdd 32 (Fin.natAdd 8 (Fin.natAdd 4 i)) := by
    apply Fin.ext
    change 44 + i.val = 32 + (8 + (4 + i.val))
    omega
  rw [hi]
  simp only [result, store, common, Fin.addCases_right]

theorem result_common {p rows : ℕ} [Fact p.Prime]
    (matrices : List (Matrix p rows)) (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool)
    (i : Fin 24) :
    (result matrices regs frame).stacks (Fin.natAdd 40 i) = common p rows frame i := by
  have hi : Fin.natAdd 40 i = Fin.natAdd 32 (Fin.natAdd 8 i) := by
    apply Fin.ext
    change 40 + i.val = 32 + (8 + i.val)
    omega
  rw [hi]
  simp only [result, store, Fin.addCases_right]

theorem result_low_empty {p rows : ℕ} [Fact p.Prime]
    (matrices : List (Matrix p rows)) (regs : Fin 16 → Bool) (frame : Fin 20 → List Bool)
    (i : Fin 32) : (result matrices regs frame).stacks (Fin.castAdd 32 i) = [] := by
  simp only [result, store, Fin.addCases_left]

theorem callbackCost_le {p rows : ℕ} [Fact p.Prime] (M : Matrix p rows)
    (P B A : ℕ) (hP : (payload M).length ≤ P) (hB : (bankList M).length ≤ B)
    (hA : MatrixImageEnumeration.sourceBudget p M.entries ≤ A) :
    callbackCost M ≤ A + 25 * P + 8 * B + 33 := by
  have hp : (payload M).length =
      2 * M.columns + 2 * (BlockCoefficientProgram.matrixBits p M.entries).length + 2 := by
    simp [payload, Encoding.length_frame]
    omega
  unfold callbackCost
  omega

/-- Linear overhead in the number of actual matrix calls and their encoded
input/output lengths. The bound `A` is on the proved complete enumerator,
including tuple generation and scalar arithmetic. -/
theorem runtimeBound_le {p rows : ℕ} [Fact p.Prime] (matrices : List (Matrix p rows))
    (P B A : ℕ)
    (hP : ∀ M ∈ matrices, (payload M).length ≤ P)
    (hB : ∀ M ∈ matrices, (bankList M).length ≤ B)
    (hA : ∀ M ∈ matrices, MatrixImageEnumeration.sourceBudget p M.entries ≤ A) :
    runtimeBound matrices ≤ 9 * commonSize p rows + 50 +
      matrices.length * (A + 31 * P + 28 * B + 60) := by
  have hbudget : RecordMappedPrograms.budget payload callbackCost matrices ≤
      matrices.length * (A + 31 * P + 8 * B + 40) := by
    induction matrices with
    | nil => simp [RecordMappedPrograms.budget]
    | cons M matrices ih =>
        have hm := callbackCost_le M P B A (hP M (by simp)) (hB M (by simp)) (hA M (by simp))
        have ht := ih (fun N hN => hP N (by simp [hN]))
          (fun N hN => hB N (by simp [hN])) (fun N hN => hA N (by simp [hN]))
        have hp := hP M (by simp)
        simp only [RecordMappedPrograms.budget, List.length_cons, Nat.add_mul, one_mul]
        omega
  have hout : (ProgramEncoding.encodeRecords ((matrices.map bankList).reverse)).length ≤
      1 + (2 * B + 2) * matrices.length := by
    have h := ProgramEncoding.encodeRecords_length_le ((matrices.map bankList).reverse) B (by
      intro bits hbits
      obtain ⟨M, hM, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hbits)
      exact hB M hM)
    simpa only [List.length_reverse, List.length_map] using h
  have hscale := Nat.mul_le_mul_left 10 hout
  calc
    runtimeBound matrices ≤ 9 * commonSize p rows + 40 +
        matrices.length * (A + 31 * P + 8 * B + 40) +
        10 * (1 + (2 * B + 2) * matrices.length) := by
      unfold runtimeBound stageCost cleanupCost
      omega
    _ = _ := by ring

end SubexponentialSAT.SubexpNodeBankMap

end OAI.Algorithms
