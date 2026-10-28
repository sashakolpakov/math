import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram

namespace OAI.Algorithms

/-!
# Runtime one-hot alphabet generation

The unary input length r is data. Each loop iteration constructs one r-bit
one-hot word using the checked repeated-copy program and prepends its frame.
The final order is the decreasing order of the hot bit's position.
-/

namespace SubexponentialSAT.Subexp.OneHotAlphabetProgram

open BitProgram StructuredCalls TupleProgram

abbrev Data := State 5 7
abbrev zeros (n : ℕ) := List.replicate n false
abbrev unary (n : ℕ) := List.replicate n true

def word (i n : ℕ) : List Bool := zeros i ++ true :: zeros n

def rows : ℕ → ℕ → List (List Bool)
  | _, 0 => []
  | i, n + 1 => rows (i + 1) n ++ [word i n]

def state (regs : Fin 5 → Bool) (i n : ℕ) (out : List Bool) : Data :=
  ⟨regs, ![unary n, zeros i, [], [], [], [false], out]⟩

def copied (src dst : Fin 7) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

abbrev copy (src dst : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.copyProgram src dst 4 0 1)

theorem copy_eval (src dst : Fin 7) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 4) (hd : (4 : Fin 7) ≠ dst)
    (h4 : d.stacks 4 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  TupleProgram.copy_eval src dst 4 0 1 hsd hs hd (by decide) d h4

def repeatRegisters : Fin 3 → Fin 5 := Fin.castAdd 2
def repeatStacks : Fin 4 → Fin 7 := ![5, 2, 4, 3]

theorem repeatRegisters_injective : Function.Injective repeatRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)

theorem repeatStacks_injective : Function.Injective repeatStacks := by decide

abbrev repeatZeros : Cmd 5 7 :=
  .call (ProgramLinking.liftProgram BlockCopyProgram.program repeatRegisters repeatStacks)

def repeatState (regs : Fin 5 → Bool) (i n : ℕ) (bits count out : List Bool) : Data :=
  ⟨regs, ![unary n, zeros i, bits, count, [], [false], out]⟩

def resetThree (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  fun j => if j.val < 3 then false else regs j

theorem repeatZeros_eval (regs : Fin 5 → Bool) (i n : ℕ) (bits out : List Bool)
    (hr : ∀ j : Fin 3, regs (repeatRegisters j) = false) :
    Eval repeatZeros (14 * n + 3)
      (repeatState regs i n bits (unary n) out)
      (repeatState (resetThree regs) i n (zeros n ++ bits) [] out) := by
  let a := repeatState regs i n bits (unary n) out
  let b := repeatState (resetThree regs) i n (zeros n ++ bits) [] out
  have hc : BlockCopyProgram.copies n [false] = zeros n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [BlockCopyProgram.copies_succ, ih, List.replicate_succ']
  have ha : embedState repeatRegisters repeatStacks a
      (BlockCopyProgram.initialState n [false] bits) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ repeatRegisters_injective repeatStacks_injective
    · intro j; fin_cases j <;>
        simpa [a, repeatState, BlockCopyProgram.initialState, BlockCopyProgram.data] using hr _
    · intros; rfl
    · intro j; fin_cases j <;> rfl
    · intros; rfl
  have hb : embedState repeatRegisters repeatStacks a
      (BlockCopyProgram.data false false [false] (zeros n ++ bits) []) = b := by
    apply embedState_eq_of_ports _ _ _ _ _ repeatRegisters_injective repeatStacks_injective
    · intro j; fin_cases j <;> rfl
    · intro j hj
      have h3 : 3 ≤ j.val := by
        by_contra h
        exact hj ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
      simp [b, a, repeatState, resetThree, Nat.not_lt.mpr h3]
    · intro j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j <;> first | rfl | exact (hj ⟨0, rfl⟩).elim |
        exact (hj ⟨1, rfl⟩).elim | exact (hj ⟨2, rfl⟩).elim | exact (hj ⟨3, rfl⟩).elim
  have ht := BlockCopyProgram.program_trace n [false] bits
  rw [hc] at ht
  have h := eval_call_lifted BlockCopyProgram.program repeatRegisters repeatStacks a
    repeatRegisters_injective repeatStacks_injective ht
  simpa only [repeatZeros, ha, hb, List.length_singleton, Nat.mul_one,
    Nat.reduceAdd, Nat.mul_comm] using h

def emitter : RecordPrograms.Ports 5 7 :=
  ⟨0, 1, 2, 2, 6, by decide, by decide, by decide, by decide⟩

abbrev zeroThird : Cmd 5 7 := .base (.atom (.set 2 false))
def zeroedThird (d : Data) : Data := ⟨Function.update d.regs 2 false, d.stacks⟩

abbrev body : Cmd 5 7 :=
  .seq (copy 1 2) (.seq (pushConst 2 0 true) (.seq (copy 0 3)
    (.seq zeroThird (.seq repeatZeros (.seq (pushConst 6 0 false)
      (.seq (escape emitter) (.seq (pushConst 6 0 true) (pushConst 1 0 false))))))))

def bodyCost (i n : ℕ) : ℕ := 12 * i + 26 * n + 30

theorem body_eval (regs : Fin 5 → Bool) (i n : ℕ) (out : List Bool) :
    ∃ rf, Eval body (bodyCost i n) (state regs i n out)
      (state rf (i + 1) n (true :: Encoding.frame (word i n) ++ out)) := by
  let a := state regs i n out
  let b := copied 1 2 a
  let c := pushedState 2 0 true b
  let d := copied 0 3 c
  let e := zeroedThird d
  let f := repeatState (resetThree e.regs) i n (zeros n ++ true :: zeros i) [] out
  let g := pushedState 6 0 false f
  let h := escapedState emitter g
  let j := pushedState 6 0 true h
  let k := pushedState 1 0 false j
  have h1 := copy_eval 1 2 a (by decide) (by decide) (by decide) rfl
  have h2 := pushConst_eval 2 0 true b
  have h3 := copy_eval 0 3 c (by decide) (by decide) (by decide) rfl
  have h4 : Eval zeroThird 1 d e := .base (.atom _ _)
  have he : e = repeatState e.regs i n (true :: zeros i) (unary n) out := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext j
    fin_cases j <;> simp [ d, c, b, a, copied,
      StackRoutines.copyStacks, state ]
  have hr : ∀ j : Fin 3, e.regs (repeatRegisters j) = false := by
    intro j
    fin_cases j <;> simp [e, zeroedThird, d, copied, repeatRegisters, readRegs]
  have h5 := repeatZeros_eval e.regs i n (true :: zeros i) out hr
  rw [← he] at h5
  have h6 := pushConst_eval 6 0 false f
  have h7 := escape_eval_state emitter g
  have h8 := pushConst_eval 6 0 true h
  have h9 := pushConst_eval 1 0 false j
  have hk : k = state k.regs (i + 1) n (true :: Encoding.frame (word i n) ++ out) := by
    apply congrArg (StructuredProgram.State.mk k.regs)
    funext v
    fin_cases v <;> simp [ j, h, g, f, emitter,
      repeatState, word, frame_eq_escaped, List.reverse_append,
      List.replicate_succ, List.append_assoc]
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  change Eval body _ a k at ht
  rw [hk] at ht
  refine ⟨k.regs, ?_⟩
  convert ht using 1
  simp [bodyCost, a, state, b, copied, c, f, g, emitter, repeatState,
    StackRoutines.copyStacks]
  omega

def loopPorts : UnaryForPrograms.Ports 5 7 := ⟨0, 3, 4⟩
abbrev enumerate : Cmd 5 7 := UnaryForPrograms.forCmd loopPorts body

def poppedRegs (regs : Fin 5 → Bool) (n : ℕ) : Fin 5 → Bool :=
  readRegs regs 3 4 (unary n).head?

theorem popped_state (regs : Fin 5 → Bool) (i n : ℕ) (out : List Bool) :
    UnaryForPrograms.popped loopPorts (state regs i n out) =
      state (poppedRegs regs n) i (n - 1) out := by
  apply congrArg (StructuredProgram.State.mk _)
  funext j
  fin_cases j <;> simp [ loopPorts, state,
    List.tail_replicate]

theorem visits (i n : ℕ) (regs : Fin 5 → Bool) (acc : List (List Bool)) :
    ∃ costs ticks rf,
      UnaryForPrograms.Visits loopPorts body costs ticks
        (state regs i n (ProgramEncoding.encodeRecords acc))
        (state rf (i + n) 0 (ProgramEncoding.encodeRecords (rows i n ++ acc))) ∧
      ticks ≤ 40 * (n + 1) * (i + n + 1) := by
  induction n generalizing i regs acc with
  | zero =>
      refine ⟨[], 2, poppedRegs regs 0, ?_, by nlinarith⟩
      have h := UnaryForPrograms.Visits.done
        (p := loopPorts) (body := body) (state regs i 0 (ProgramEncoding.encodeRecords acc)) rfl
      simpa only [popped_state, Nat.zero_sub, Nat.add_zero, rows, List.nil_append] using h
  | succ n ih =>
      obtain ⟨rf, hb⟩ := body_eval (poppedRegs regs (n + 1)) i n
        (ProgramEncoding.encodeRecords acc)
      have hbits : true :: Encoding.frame (word i n) ++ ProgramEncoding.encodeRecords acc =
          ProgramEncoding.encodeRecords (word i n :: acc) := rfl
      rw [hbits] at hb
      obtain ⟨costs, ticks, rg, ht, hbound⟩ := ih (i + 1) rf (word i n :: acc)
      have hp : UnaryForPrograms.popped loopPorts
          (state regs i (n + 1) (ProgramEncoding.encodeRecords acc)) =
          state (poppedRegs regs (n + 1)) i n (ProgramEncoding.encodeRecords acc) := by
        rw [popped_state, Nat.add_sub_cancel]
      rw [← hp] at hb
      have hc : (state rf (i + 1) n (ProgramEncoding.encodeRecords (word i n :: acc))).stacks
          loopPorts.counter = (UnaryForPrograms.popped loopPorts
            (state regs i (n + 1) (ProgramEncoding.encodeRecords acc))).stacks loopPorts.counter := by
        rw [hp]
        rfl
      have h := UnaryForPrograms.Visits.step (p := loopPorts) (body := body)
        (by simp [state, loopPorts]) hb hc ht
      refine ⟨bodyCost i n :: costs, bodyCost i n + ticks + 2, rg, ?_, ?_⟩
      · simpa only [rows, List.append_assoc, List.singleton_append, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using h
      · dsimp [bodyCost]
        nlinarith

def inputState (regs : Fin 5 → Bool) (n : ℕ) : Data :=
  ⟨regs, ![unary n, [], [], [], [], [], []]⟩

def outputState (n : ℕ) : Data :=
  ⟨fun _ => false, ![[], [], [], [], [], [], ProgramEncoding.encodeRecords (rows 0 n)]⟩

abbrev reset : Cmd 5 7 := .base (CandidateScoreProgram.resetList (List.finRange 5))
abbrev command : Cmd 5 7 :=
  .seq (pushConst 5 0 false) (.seq (pushConst 6 0 false) (.seq enumerate
    (.seq (.call (StackRoutines.clearProgram 1 0 1))
      (.seq (.call (StackRoutines.clearProgram 5 0 1)) reset))))

theorem command_eval (regs : Fin 5 → Bool) (n : ℕ) :
    ∃ ticks, ticks ≤ 60 * (n + 1) ^ 2 ∧
      Eval command ticks (inputState regs n) (outputState n) := by
  let a := inputState regs n
  let b := pushedState 5 0 false a
  let c := pushedState 6 0 false b
  have hc : c = state c.regs 0 n (ProgramEncoding.encodeRecords []) := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext j
    fin_cases j <;> rfl
  obtain ⟨costs, ticks, rf, hv, ht⟩ := visits 0 n c.regs []
  simp only [Nat.zero_add, List.append_nil] at hv
  have hr := hv.eval
  rw [← hc] at hr
  let d := state rf n 0 (ProgramEncoding.encodeRecords (rows 0 n))
  let e : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 1 d.stacks⟩
  let f : Data := ⟨readRegs e.regs 0 1 none, StackRoutines.clearStacks 5 e.stacks⟩
  have h1 := pushConst_eval 5 0 false a
  have h2 := pushConst_eval 6 0 false b
  have h4 := TupleProgram.clear_eval 1 0 1 d
  have h5 := TupleProgram.clear_eval 5 0 1 e
  have h6 := Eval.base (CandidateScoreProgram.resetList_eval (List.finRange 5) f)
  have hreset : (⟨CandidateScoreProgram.resetValues (List.finRange 5) f.regs, f.stacks⟩ : Data) =
      outputState n := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      simp [CandidateScoreProgram.resetValues_apply]
    · funext j
      fin_cases j <;> simp [f, e, d, state, StackRoutines.clearStacks ]
  rw [hreset] at h6
  have h := h1.seq (h2.seq (hr.seq (h4.seq (h5.seq h6))))
  change Eval command _ a (outputState n) at h
  refine ⟨_, ?_, h⟩
  have hd : (d.stacks 1).length = n := by simp [d, state]
  have he : (e.stacks 5).length = 1 := by simp [e, d, state, StackRoutines.clearStacks]
  simp only [hd, he, List.length_finRange]
  nlinarith

abbrev program : Program 5 7 (size command + 1) := compiled command 0 6

theorem program_runsIn (regs : Fin 5 → Bool) (n : ℕ) :
    RunsIn program (60 * (n + 1) ^ 2 + 1)
      ((inputState regs n).withPC (some program.entry)) ((outputState n).withPC none) := by
  obtain ⟨ticks, ht, he⟩ := command_eval regs n
  exact ⟨ticks + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 6⟩

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
