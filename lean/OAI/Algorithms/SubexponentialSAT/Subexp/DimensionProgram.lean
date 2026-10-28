import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-!
# A fixed generator for all unary dimensions from zero through a runtime bound

The input bound is a unary stack, and the output is a framed list of unary
payloads. The program has no bound-dependent control labels.
-/

namespace SubexponentialSAT.Subexp.DimensionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram

def emitPorts : RecordPrograms.Ports 5 5 :=
  ⟨2, 3, 4, 2, 3, by decide, by decide, by decide, by decide⟩

abbrev emitCurrent : Cmd 5 5 :=
  .seq (pushConst 3 2 false)
    (.seq (.call (StackRoutines.copyProgram 1 2 4 2 3))
      (.seq (escape emitPorts) (pushConst 3 2 true)))

/-- Stack 0 is the remaining unary bound, stack 1 the current unary value,
stack 3 the accumulated framed records; stacks 2 and 4 are empty scratch. -/
def Ready (k : ℕ) (remaining : List Bool) (accum : Records) (a : State 5 5) : Prop :=
  a.stacks 0 = remaining ∧ a.stacks 1 = List.replicate k true ∧
  a.stacks 2 = [] ∧ a.stacks 3 = ProgramEncoding.encodeRecords accum ∧ a.stacks 4 = []

theorem emitCurrent_eval (k : ℕ) (remaining : List Bool) (accum : Records)
    (a : State 5 5) (ha : Ready k remaining accum a) :
    ∃ b, Ready k remaining (List.replicate k true :: accum) b ∧
      b.regs 0 = a.regs 0 ∧ b.regs 1 = a.regs 1 ∧ Eval emitCurrent (12 * k + 12) a b := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  let b := pushedState 3 2 false a
  let c : State 5 5 :=
    ⟨readRegs b.regs 2 3 none, StackRoutines.copyStacks 1 2 b.stacks⟩
  let d := escapedState emitPorts c
  let e := pushedState 3 2 true d
  have t1 := pushConst_eval 3 2 false a
  have t2 := copy_eval 1 2 4 2 3 (by decide) (by decide) (by decide) (by decide) b
    (by simpa [b, pushedState] using h4)
  have t3 := escape_eval_state emitPorts c
  have t4 := pushConst_eval 3 2 true d
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · simp [Ready, e,d,c,b, emitPorts, StackRoutines.copyStacks,
      h0,h1,h2,h3,h4,ProgramEncoding.encodeRecords,Encoding.encodeList,
      frame_eq_escaped,List.append_assoc]
  · simp [e,d,c,b,emitPorts,readRegs]
  · simp [e,d,c,b,emitPorts,readRegs]
  · convert t1.seq (t2.seq (t3.seq t4)) using 1 ;
      simp [b,c,StackRoutines.copyStacks,emitPorts,h1,h2] ; omega

abbrev readCounter : Cmd 5 5 := RecordPrograms.atom (.pop 0 0 1)
def readCounterState (a : State 5 5) : State 5 5 :=
  ⟨readRegs a.regs 0 1 (a.stacks 0).head?, Function.update a.stacks 0 (a.stacks 0).tail⟩

theorem readCounter_eval (a : State 5 5) :
    Eval readCounter 1 a (readCounterState a) := .base (.atom _ _)

abbrev increment : Cmd 5 5 := pushConst 1 2 true
abbrev loop : Cmd 5 5 := .while 1 (.seq emitCurrent (.seq increment readCounter))
abbrev enumerate : Cmd 5 5 := .seq readCounter loop

/-- Descending unary records, including both endpoints. -/
def dimensionRows (k : ℕ) : ℕ → Records
  | 0 => [List.replicate k true]
  | n + 1 => dimensionRows (k + 1) n ++ [List.replicate k true]

/-- Exact cost of the bound-consuming loop, excluding its final endpoint. -/
def loopCost (k : ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => (12 * k + 12) + 2 + loopCost (k + 1) n + 2

def earlierRows (k : ℕ) : ℕ → Records
  | 0 => []
  | n + 1 => earlierRows (k + 1) n ++ [List.replicate k true]

theorem enumerate_eval (k : ℕ) (remaining : List Bool) (accum : Records)
    (a : State 5 5) (ha : Ready k remaining accum a) :
    ∃ b, Ready (k + remaining.length) [] (earlierRows k remaining.length ++ accum) b ∧
      b.regs 1 = false ∧ Eval enumerate (loopCost k remaining.length) a b := by
  induction remaining generalizing k accum a with
  | nil =>
      let b := readCounterState a
      have hb : Ready k [] accum b := by
        rcases ha with ⟨h0,h1,h2,h3,h4⟩
        simp [Ready,b,readCounterState,h0,h1,h2,h3,h4]
      have hr : b.regs 1 = false := by simp [b,readCounterState,readRegs,ha.1]
      refine ⟨b, by simpa [earlierRows] using hb, hr, ?_⟩
      exact (readCounter_eval a).seq (Eval.while_false hr)
  | cons bit remaining ih =>
      let b := readCounterState a
      have hb : Ready k remaining accum b := by
        rcases ha with ⟨h0,h1,h2,h3,h4⟩
        simp [Ready,b,readCounterState,h0,h1,h2,h3,h4]
      have hr : b.regs 1 = true := by simp [b,readCounterState,readRegs,ha.1]
      obtain ⟨c,hc,hc0,hc1,he⟩ := emitCurrent_eval k remaining accum b hb
      let d := pushedState 1 2 true c
      have hd : Ready (k + 1) remaining (List.replicate k true :: accum) d := by
        rcases hc with ⟨h0,h1,h2,h3,h4⟩
        simp [Ready,d,h0,h1,h2,h3,h4,List.replicate_succ]
      obtain ⟨e,hs,hr',ht⟩ := ih (k + 1) (List.replicate k true :: accum) d hd
      refine ⟨e, ?_, hr', ?_⟩
      · simpa [earlierRows,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,
          Nat.add_comm] using hs
      · generalize hsteps : loopCost (k + 1) remaining.length = steps at ht
        cases ht with
        | @seq first second n m x y z hp hl =>
            have h := (readCounter_eval a).seq
              (Eval.while_true hr (he.seq ((pushConst_eval 1 2 true c).seq hp)) hl)
            convert h using 1 ; simp only [loopCost,List.length_cons] ; omega

theorem dimensionRows_eq (k n : ℕ) :
    dimensionRows k n = List.replicate (k + n) true :: earlierRows k n := by
  induction n generalizing k with
  | zero => simp [dimensionRows,earlierRows]
  | succ n ih => simp [dimensionRows,earlierRows,ih,Nat.add_left_comm,
      Nat.add_comm]

abbrev generateCmd : Cmd 5 5 := .seq (pushConst 3 2 false) (.seq enumerate emitCurrent)
def program := StructuredCalls.compiled generateCmd 0 3

theorem control_size : StructuredCalls.size generateCmd + 1 = 44 := rfl

theorem generate_eval (remaining : List Bool) (a : State 5 5)
    (h0 : a.stacks 0 = remaining) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Ready remaining.length [] (dimensionRows 0 remaining.length) b ∧
      Eval generateCmd (2 + loopCost 0 remaining.length + (12 * remaining.length + 12)) a b := by
  let c := pushedState 3 2 false a
  have hc : Ready 0 remaining [] c := by
    simp [Ready,c,h0,h1,h2,h3,h4,ProgramEncoding.encodeRecords,Encoding.encodeList]
  obtain ⟨d,hd,_,ht⟩ := enumerate_eval 0 remaining [] c hc
  simp only [Nat.zero_add,List.append_nil] at hd
  obtain ⟨e,he,_,_,hu⟩ := emitCurrent_eval remaining.length []
    (earlierRows 0 remaining.length) d hd
  refine ⟨e, ?_, ?_⟩
  · simpa only [dimensionRows_eq,Nat.zero_add] using he
  · have h := (pushConst_eval 3 2 false a).seq (ht.seq hu)
    simpa only [Nat.add_assoc] using h

theorem program_runsIn (remaining : List Bool) (a : State 5 5)
    (h0 : a.stacks 0 = remaining) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Ready remaining.length [] (dimensionRows 0 remaining.length) b ∧
      RunsIn program (loopCost 0 remaining.length + 12 * remaining.length + 15)
        (a.withPC (some program.entry)) (b.withPC none) := by
  obtain ⟨b,hb,ht⟩ := generate_eval remaining a h0 h1 h2 h3 h4
  refine ⟨b,hb,_,by omega,StructuredCalls.compiled_halt_trace ht 0 3⟩

theorem dimensionRows_length (k n : ℕ) : (dimensionRows k n).length = n + 1 := by
  induction n generalizing k with
  | zero => simp [dimensionRows]
  | succ n ih => simp [dimensionRows,ih]

theorem mem_dimensionRows (k n d : ℕ) :
    List.replicate d true ∈ dimensionRows k n ↔ k ≤ d ∧ d ≤ k + n := by
  induction n generalizing k with
  | zero =>
      simp only [dimensionRows, List.mem_singleton, Nat.add_zero]
      constructor
      · intro h
        have he := congrArg List.length h
        simp only [List.length_replicate] at he
        omega
      · rintro ⟨h1,h2⟩
        have he : d = k := by omega
        simp [he]
  | succ n ih =>
      simp only [dimensionRows,List.mem_append,List.mem_singleton,ih]
      have hrep : List.replicate d true = List.replicate k true ↔ d = k := by
        constructor
        · intro h; simpa using congrArg List.length h
        · intro h; simp [h]
      rw [hrep]
      omega

theorem loopCost_eq (k n : ℕ) :
    loopCost k n = 6 * n ^ 2 + (12 * k + 10) * n + 2 := by
  induction n generalizing k with
  | zero => simp [loopCost]
  | succ n ih => rw [loopCost, ih]; ring

theorem program_runsIn_quadratic (remaining : List Bool) (a : State 5 5)
    (h0 : a.stacks 0 = remaining) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Ready remaining.length [] (dimensionRows 0 remaining.length) b ∧
      RunsIn program (6 * remaining.length ^ 2 + 22 * remaining.length + 17)
        (a.withPC (some program.entry)) (b.withPC none) := by
  obtain ⟨b,hb,ht⟩ := program_runsIn remaining a h0 h1 h2 h3 h4
  refine ⟨b,hb,?_⟩
  convert ht using 1
  rw [loopCost_eq]
  ring

theorem program_primitive_runsIn (remaining : List Bool) (a : State 5 5)
    (h0 : a.stacks 0 = remaining) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Ready remaining.length [] (dimensionRows 0 remaining.length) b ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program *
          (6 * remaining.length ^ 2 + 22 * remaining.length + 17))
        (BitProgram.primitiveCfg program (a.withPC (some program.entry)))
        (BitProgram.primitiveCfg program (b.withPC none)) := by
  obtain ⟨b,hb,ht⟩ := program_runsIn_quadratic remaining a h0 h1 h2 h3 h4
  exact ⟨b,hb,BitProgram.primitive_execution program ht⟩

end SubexponentialSAT.Subexp.DimensionProgram

end OAI.Algorithms
