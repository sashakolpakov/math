import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorage

namespace OAI.Algorithms

/-! Actual framing of selected local basis tables and split dimensions. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

def framePorts (dst : Fin 128) (h : dst ≠ 0) : RecordPrograms.Ports 32 128 :=
  ⟨0, 1, 2, 0, dst, by decide, by decide, by decide, Ne.symm h⟩

def frameForward (src dst : Fin 128) (h : dst ≠ 0) : Code :=
  .seq (transfer src 0)
    (.seq (TupleProgram.pushConst dst 0 false) (TupleProgram.escape (framePorts dst h)))

def framedState (src dst : Fin 128) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks src []) dst
      (Encoding.frame (a.stacks src) ++ a.stacks dst)⟩

theorem frameForward_eval (src dst : Fin 128) (a : Data)
    (hs : src ≠ 0) (hd : dst ≠ 0) (hsd : src ≠ dst) (h0 : a.stacks 0 = []) :
    Eval (frameForward src dst hd) (8 * (a.stacks src).length + 8) a
      (framedState src dst a) := by
  let b := transferState src 0 a
  let c := TupleProgram.pushedState dst 0 false b
  have ht := transfer_eval src 0 a hs
  have hp := TupleProgram.pushConst_eval dst (0 : Fin 32) false b
  have he := TupleProgram.escape_eval_state (framePorts dst hd) c
  have hc0 : c.stacks 0 = (a.stacks src).reverse := by
    simp [c, b, transferState, StackRoutines.transferStacks,
      hd, Ne.symm hd, h0]
  have hout : TupleProgram.escapedState (framePorts dst hd) c = framedState src dst a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
        simp [framePorts, c, b, transferState, readRegs, Function.update_apply, hj0, hj1]
    · funext j
      by_cases hjd : j = dst
      · subst j
        simp [framePorts, c, b, transferState, StackRoutines.transferStacks,
          hd, Ne.symm hd, Ne.symm hsd, h0, TupleProgram.frame_eq_escaped,
          List.append_assoc]
      · by_cases hjs : j = src
        · subst j
          simp [framePorts, c, b, transferState, StackRoutines.transferStacks, hs, hsd]
        · by_cases hj0 : j = 0
          · subst j
            simp [framePorts, c, b, transferState, StackRoutines.transferStacks,
              hd, Ne.symm hs, Ne.symm hd, h0]
          · simp [framePorts, c, b, transferState, StackRoutines.transferStacks,
              hjd, hjs, hj0]
  rw [hout] at he
  have hl : (c.stacks (framePorts dst hd).source).length = (a.stacks src).length := by
    simp only [framePorts, hc0, List.length_reverse]
  rw [hl] at he
  have h := ht.seq (hp.seq he)
  have hcost : 3 * (a.stacks src).length + 3 +
      (2 + (5 * (a.stacks src).length + 3)) =
      8 * (a.stacks src).length + 8 := by
    omega
  rw [hcost] at h
  exact h

def appendRecord (src dst : Fin 128) : Code :=
  .seq (frameForward src 125 (by decide))
    (.seq (TupleProgram.pushConst 125 0 true) (transfer 125 dst))

def recordedState (src dst : Fin 128) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks src []) dst
      ((true :: Encoding.frame (a.stacks src)).reverse ++ a.stacks dst)⟩

theorem appendRecord_eval (src dst : Fin 128) (a : Data)
    (hs : src ≠ 0) (hs125 : src ≠ 125) (hd125 : dst ≠ 125) (hsd : src ≠ dst)
    (h0 : a.stacks 0 = []) (h125 : a.stacks 125 = []) :
    Eval (appendRecord src dst) (14 * (a.stacks src).length + 19) a
      (recordedState src dst a) := by
  let b := framedState src 125 a
  let c := TupleProgram.pushedState 125 0 true b
  have hf := frameForward_eval src 125 a hs (by decide) hs125 h0
  have hp := TupleProgram.pushConst_eval (125 : Fin 128) (0 : Fin 32) true b
  have ht := transfer_eval 125 dst c (Ne.symm hd125)
  have hc125 : c.stacks 125 = true :: Encoding.frame (a.stacks src) := by
    simp [c, b, framedState, h125]
  have hout : transferState 125 dst c = recordedState src dst a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
        simp [c, b, framedState, readRegs, hj0, hj1]
    · funext j
      by_cases hjd : j = dst
      · subst j
        simp [StackRoutines.transferStacks, c, b, framedState, h125, hd125,
          Ne.symm hsd]
      · by_cases hj125 : j = 125
        · subst j
          simp [StackRoutines.transferStacks, c, b, framedState, h125,
            Ne.symm hs125, hd125, Ne.symm hd125]
        · simp [StackRoutines.transferStacks, c, b, framedState, hjd, hj125]
  rw [hout] at ht
  have hl : (c.stacks 125).length = 2 * (a.stacks src).length + 2 := by
    rw [hc125]
    simp only [List.length_cons, Encoding.length_frame]
  rw [hl] at ht
  have h := hf.seq (hp.seq ht)
  have hcost : 8 * (a.stacks src).length + 8 +
      (2 + (3 * (2 * (a.stacks src).length + 2) + 3)) =
      14 * (a.stacks src).length + 19 := by
    omega
  rw [hcost] at h
  exact h

def resultPayload (N d table : Word) : Word :=
  Encoding.frame N ++ Encoding.frame d ++ Encoding.frame table

def emitResult : Code :=
  .seq (frameForward 106 126 (by decide))
    (.seq (frameForward 73 126 (by decide))
      (.seq (frameForward 123 126 (by decide)) (appendRecord 126 122)))

def emittedResult (a : Data) : Data :=
  recordedState 126 122 (framedState 123 126 (framedState 73 126 (framedState 106 126 a)))

theorem resultPayload_length (N d table : Word) :
    (resultPayload N d table).length = 2 * (N.length + d.length + table.length) + 3 := by
  simp only [resultPayload, List.length_append, Encoding.length_frame]
  omega

theorem emitResult_eval (a : Data) (h0 : a.stacks 0 = [])
    (h125 : a.stacks 125 = []) (h126 : a.stacks 126 = []) :
    Eval emitResult
      (36 * ((a.stacks 123).length + (a.stacks 73).length + (a.stacks 106).length) + 85)
      a (emittedResult a) := by
  let b := framedState 106 126 a
  let c := framedState 73 126 b
  let d := framedState 123 126 c
  have hb0 : b.stacks 0 = [] := by simp [b, framedState, h0]
  have hc0 : c.stacks 0 = [] := by simp [c, b, framedState, h0]
  have hd0 : d.stacks 0 = [] := by simp [d, c, b, framedState, h0]
  have hd125 : d.stacks 125 = [] := by simp [d, c, b, framedState, h125]
  have hb73 : b.stacks 73 = a.stacks 73 := by simp [b, framedState]
  have hc123 : c.stacks 123 = a.stacks 123 := by simp [c, b, framedState]
  have hd126 : d.stacks 126 = resultPayload (a.stacks 123) (a.stacks 73) (a.stacks 106) := by
    simp [d, c, b, framedState, resultPayload, h126, List.append_assoc]
  have h1 := frameForward_eval 106 126 a (by decide) (by decide) (by decide) h0
  have h2 := frameForward_eval 73 126 b (by decide) (by decide) (by decide) hb0
  have h3 := frameForward_eval 123 126 c (by decide) (by decide) (by decide) hc0
  have h4 := appendRecord_eval 126 122 d (by decide) (by decide) (by decide)
    (by decide) hd0 hd125
  rw [hb73] at h2
  rw [hc123] at h3
  rw [hd126, resultPayload_length] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  have hcost :
      8 * (a.stacks 106).length + 8 +
        (8 * (a.stacks 73).length + 8 +
          (8 * (a.stacks 123).length + 8 +
            (14 * (2 * ((a.stacks 123).length + (a.stacks 73).length +
              (a.stacks 106).length) + 3) + 19))) =
      36 * ((a.stacks 123).length + (a.stacks 73).length +
        (a.stacks 106).length) + 85 := by
    omega
  rw [hcost] at h
  exact h

theorem emittedResult_output (a : Data) (h126 : a.stacks 126 = []) :
    (emittedResult a).stacks 122 =
      (true :: Encoding.frame (resultPayload (a.stacks 123) (a.stacks 73) (a.stacks 106))).reverse ++
        a.stacks 122 := by
  simp [emittedResult, recordedState, framedState, resultPayload, h126, List.append_assoc]

theorem emittedResult_frame (a : Data) (j : Fin 128)
    (hN : j ≠ 123) (hd : j ≠ 73) (hC : j ≠ 106) (ho : j ≠ 122)
    (h126 : a.stacks 126 = []) :
    (emittedResult a).stacks j = a.stacks j := by
  by_cases hj : j = 126
  · subst j
    simp [emittedResult, recordedState, framedState, h126]
  · simp [emittedResult, recordedState, framedState, hN, hd, hC, ho, hj]

theorem emittedResult_sources (a : Data) :
    (emittedResult a).stacks 106 = [] ∧
    (emittedResult a).stacks 73 = [] ∧
    (emittedResult a).stacks 123 = [] := by
  simp [emittedResult, recordedState, framedState]

theorem emittedResult_registers (a : Data) (j : Fin 32) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (emittedResult a).regs j = a.regs j := by
  simp [emittedResult, recordedState, framedState, readRegs, h0, h1]

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
