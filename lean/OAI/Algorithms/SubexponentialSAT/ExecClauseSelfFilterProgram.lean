import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseFilterReverse

namespace OAI.Algorithms

/-!
# Complete fixed-master clause filtering

This wrapper performs the actual initial copy, record scan, cleanup, and
record-order restoration. Its input and output are on stack 13; every other
stack is empty at both boundaries.
-/

namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)


abbrev selfFilter (mode : Mode) : Cmd 15 16 :=
  .seq copyMaster (.seq (pushFalse 14) (.seq (filterScan mode)
    (.seq (clear 12) (.seq (pushFalse 13) ExecClauseFilterReverse.command))))

/-- A complete finite-program execution; the master copy and all temporary
records have been consumed when the ordered output is returned. -/
theorem selfFilter_eval (mode : Mode) (F : Formula) (regs : Regs) :
    ∃ n ≤ 999 * ((encodeFormula F).length + 1) ^ 2, ∃ rf : Regs,
      Eval (selfFilter mode) n
        (state regs [] [] [] (encodeFormula F) [] [])
        (state rf [] [] [] (encodeFormula (filtered mode F F)) [] []) := by
  let firstRegs := Function.update (reset regs) 0 false
  obtain ⟨n, hn, rf, hscan⟩ := filterScan_eval mode F F [] firstRegs
  simp only [List.append_nil] at hscan
  let finalRegs := Function.update (reset rf) 0 false
  obtain ⟨m, hm, hreverse⟩ := ExecClauseFilterReverse.reverse_eval
    (formulaRecords (filtered mode F F)).reverse [] finalRegs
  change Eval ExecClauseFilterReverse.command m
    (state finalRegs [] [] [] (Encoding.encodeList id [])
      (Encoding.encodeList id (formulaRecords (filtered mode F F)).reverse) [])
    (state (flags finalRegs false true false) [] [] []
      (Encoding.encodeList id ((formulaRecords (filtered mode F F)).reverse.reverse ++ [])) [] [])
    at hreverse
  simp only [List.reverse_reverse, List.append_nil, ← encodeFormula_records] at hreverse
  rw [encoded_reverse_length, ← encodeFormula_records] at hm
  have hlength := filtered_length_le mode F F
  have hfull := (copyMaster_eval regs (encodeFormula F) [] []).seq
    ((pushOutput_eval (reset regs) (encodeFormula F) (encodeFormula F) [] []).seq
      (hscan.seq ((clearMaster_eval rf (encodeFormula F) []
        (Encoding.encodeList id (formulaRecords (filtered mode F F)).reverse) []).seq
        ((pushSource_eval (reset rf) [] []
          (Encoding.encodeList id (formulaRecords (filtered mode F F)).reverse) []).seq hreverse))))
  refine ⟨_, ?_, flags finalRegs false true false, hfull⟩
  nlinarith

def Ready (d : Data) : Prop := ∀ i : Fin 16, i ≠ 13 → d.stacks i = []

theorem state_ready (regs : Regs) (source : List Bool) :
    Ready (state regs [] [] [] source [] []) := by
  intro i hi
  fin_cases i <;> simp_all [state]

theorem ready_eq_state (d : Data) (hready : Ready d) :
    d = state d.regs [] [] [] (d.stacks 13) [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  by_cases hi : i = 13
  · subst i
    rfl
  · rw [hready i hi]
    fin_cases i <;> simp_all []

def selfFilterProgram (mode : Mode) := compiled (selfFilter mode) 13 13

/-- The concrete in-place filter returns exactly the selected ordered list,
with no hidden callback or external execution premise. -/
theorem selfFilter_runsIn (mode : Mode) (F : Formula) (d : Data)
    (hsource : d.stacks 13 = encodeFormula F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = encodeFormula (filtered mode F F) ∧
      RunsIn (selfFilterProgram mode) (1000 * ((encodeFormula F).length + 1) ^ 2)
        (d.withPC (some (selfFilterProgram mode).entry)) (e.withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := selfFilter_eval mode F d.regs
  have hd : d = state d.regs [] [] [] (encodeFormula F) [] [] := by
    simpa only [hsource] using ready_eq_state d hready
  refine ⟨state rf [] [] [] (encodeFormula (filtered mode F F)) [] [],
    state_ready _ _, rfl, n + 1, ?_, ?_⟩
  · have hpos : 0 < ((encodeFormula F).length + 1) ^ 2 := pow_pos (by omega) _
    omega
  · have ht := compiled_halt_trace he 13 13
    change Trace (selfFilterProgram mode) (n + 1)
      ((state d.regs [] [] [] (encodeFormula F) [] []).withPC
        (some (selfFilterProgram mode).entry)) _ at ht
    simpa only [← hd] using ht

theorem selfFilter_primitive_execution (mode : Mode) (F : Formula) (d : Data)
    (hsource : d.stacks 13 = encodeFormula F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = encodeFormula (filtered mode F F) ∧
      Computation.RunsIn (primitive (selfFilterProgram mode)).step
        (primitiveOverhead (selfFilterProgram mode) *
          (1000 * ((encodeFormula F).length + 1) ^ 2))
        (primitiveCfg (selfFilterProgram mode) (d.withPC (some (selfFilterProgram mode).entry)))
        (primitiveCfg (selfFilterProgram mode) (e.withPC none)) := by
  obtain ⟨e, hr, ho, ht⟩ := selfFilter_runsIn mode F d hsource hready
  exact ⟨e, hr, ho, BitProgram.primitive_execution (selfFilterProgram mode) ht⟩

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
