import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-! A fixed destructive minimum routine for unary packing counts. -/

namespace SubexponentialSAT.Subexp.PackingUnaryMin

open BitProgram StructuredCalls MatrixProgramSupport

def state (regs : Fin 8 → Bool) (left right output : List Bool) :
    StructuredProgram.State 8 3 :=
  ⟨regs, ![left, right, output]⟩

abbrev core : Program 8 3 8 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .pop 1 0 2 2
    | 2 => .branch 1 3 7
    | 3 => .branch 2 4 7
    | 4 => .set 0 true 5
    | 5 => .push 2 0 6
    | 6 => .goto 0
    | _ => .halt

def popped (regs : Fin 8 → Bool) (left right : Option Bool) : Fin 8 → Bool :=
  readRegs (readRegs regs 0 1 left) 0 2 right

theorem core_nil (regs : Fin 8 → Bool) (right output : List Bool) :
    Trace core 4 ((state regs [] right output).withPC (some core.entry))
      ((state (popped regs none right.head?) [] right.tail output).withPC none) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, core, execInstr, state,
    StructuredProgram.State.withPC, popped, readRegs]
  funext i
  fin_cases i <;> simp

theorem core_cons_nil (regs : Fin 8 → Bool) (bit : Bool) (left output : List Bool) :
    Trace core 5 ((state regs (bit :: left) [] output).withPC (some core.entry))
      ((state (popped regs (some bit) none) left [] output).withPC none) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, core, execInstr, state,
    StructuredProgram.State.withPC, popped, readRegs]
  funext i
  fin_cases i <;> simp

theorem core_cons (regs : Fin 8 → Bool) (x y : Bool) (left right output : List Bool) :
    Trace core 7 ((state regs (x :: left) (y :: right) output).withPC (some core.entry))
      ((state (Function.update (popped regs (some x) (some y)) 0 true)
        left right (true :: output)).withPC (some core.entry)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, core, execInstr, state,
    StructuredProgram.State.withPC, popped, readRegs]
  funext i
  fin_cases i <;> simp

theorem core_trace (left right output : List Bool) (regs : Fin 8 → Bool) :
    ∃ n ≤ 7 * min left.length right.length + 5, ∃ regs' left' right',
      Trace core n ((state regs left right output).withPC (some core.entry))
        ((state regs' left' right'
          (List.replicate (min left.length right.length) true ++ output)).withPC none) ∧
      left'.length ≤ left.length ∧ right'.length ≤ right.length := by
  induction left generalizing regs right output with
  | nil =>
    refine ⟨4, by simp, popped regs none right.head?, [], right.tail, ?_, by simp, ?_⟩
    · simpa using core_nil regs right output
    · simp
  | cons x left ih =>
    cases right with
    | nil =>
      refine ⟨5, by simp, popped regs (some x) none, left, [], ?_, by simp, by simp⟩
      simpa using core_cons_nil regs x left output
    | cons y right =>
      obtain ⟨n, hn, rf, ls, rs, ht, hl, hr⟩ := ih right (true :: output)
        (Function.update (popped regs (some x) (some y)) 0 true)
      have he := (core_cons regs x y left right output).trans ht
      have hm : min (x :: left).length (y :: right).length =
          min left.length right.length + 1 := by
        simp only [List.length_cons]
        omega
      have hout : List.replicate (min left.length right.length) true ++ true :: output =
          List.replicate (min (x :: left).length (y :: right).length) true ++ output := by
        rw [hm, List.replicate_add]
        simp [List.append_assoc]
      refine ⟨7 + n, by rw [hm]; omega,
        rf, ls, rs, ?_, by simpa using hl.trans (Nat.le_succ _),
        by simpa using hr.trans (Nat.le_succ _)⟩
      simpa only [hout] using he

abbrev command : Cmd 8 3 :=
  .seq (.call core)
    (.seq (.call (StackRoutines.clearProgram 0 0 1))
      (.call (StackRoutines.clearProgram 1 0 1)))

def program := compiled command 0 2

/-- Count words are compared by actual simultaneous pops. Both inputs are
cleared, and the result is a canonical true-unary minimum. -/
theorem program_trace (left right output : List Bool) (regs : Fin 8 → Bool) :
    ∃ n ≤ 9 * (left.length + right.length) + 12, ∃ regs',
      Trace program n ((state regs left right output).withPC (some program.entry))
        ((state regs' [] []
          (List.replicate (min left.length right.length) true ++ output)).withPC none) := by
  obtain ⟨n, hn, rf, ls, rs, ht, hl, hr⟩ := core_trace left right output regs
  let result := List.replicate (min left.length right.length) true ++ output
  let r1 := readRegs rf 0 1 none
  let r2 := readRegs r1 0 1 none
  have h0 : Eval (.call core) n (state regs left right output) (state rf ls rs result) :=
    .call _ ht
  have h1 : Eval (.call (StackRoutines.clearProgram 0 0 1)) (2 * ls.length + 3)
      (state rf ls rs result) (state r1 [] rs result) := by
    have hc := TupleProgram.clear_eval (0 : Fin 3) (0 : Fin 8) 1 (state rf ls rs result)
    have hs : (⟨r1, StackRoutines.clearStacks 0 (state rf ls rs result).stacks⟩ :
        StructuredProgram.State 8 3) = state r1 [] rs result := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext i
      fin_cases i <;> rfl
    change Eval (.call (StackRoutines.clearProgram 0 0 1)) (2 * ls.length + 3)
      (state rf ls rs result)
      (⟨r1, StackRoutines.clearStacks 0 (state rf ls rs result).stacks⟩ :
        StructuredProgram.State 8 3) at hc
    rw [hs] at hc
    exact hc
  have h2 : Eval (.call (StackRoutines.clearProgram 1 0 1)) (2 * rs.length + 3)
      (state r1 [] rs result) (state r2 [] [] result) := by
    have hc := TupleProgram.clear_eval (1 : Fin 3) (0 : Fin 8) 1 (state r1 [] rs result)
    have hs : (⟨r2, StackRoutines.clearStacks 1 (state r1 [] rs result).stacks⟩ :
        StructuredProgram.State 8 3) = state r2 [] [] result := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext i
      fin_cases i <;> rfl
    change Eval (.call (StackRoutines.clearProgram 1 0 1)) (2 * rs.length + 3)
      (state r1 [] rs result)
      (⟨r2, StackRoutines.clearStacks 1 (state r1 [] rs result).stacks⟩ :
        StructuredProgram.State 8 3) at hc
    rw [hs] at hc
    exact hc
  refine ⟨n + (2 * ls.length + 3 + (2 * rs.length + 3)) + 1, ?_, r2, ?_⟩
  · have hm := Nat.min_le_left left.length right.length
    omega
  · exact compiled_halt_trace (h0.seq (h1.seq h2)) 0 2

end SubexponentialSAT.Subexp.PackingUnaryMin

end OAI.Algorithms
