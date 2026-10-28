import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-! A fixed frame counter for the complete-block packing controller. -/

namespace SubexponentialSAT.Subexp.PackingFrameCount

open BitProgram StructuredCalls MatrixProgramSupport

abbrev state (regs : Fin 8 → Bool) (source payload count : List Bool) : StructuredProgram.State 8 3 :=
  ⟨regs, ![source, payload, count]⟩

abbrev peek : Cmd 8 3 := .base (.atom (.peek 0 0 1))
abbrev clearPayload : Cmd 8 3 := .call (StackRoutines.clearProgram 1 0 1)
abbrev increment : Cmd 8 3 := TupleProgram.pushConst 2 0 true
abbrev body : Cmd 8 3 := .seq (readFrame 0 1 (by decide))
  (.seq clearPayload (.seq increment peek))
abbrev loop : Cmd 8 3 := .while 1 body
abbrev command : Cmd 8 3 := .seq peek loop
def program := compiled command 0 2

abbrev ready (regs : Fin 8 → Bool) (source count : List Bool) : StructuredProgram.State 8 3 :=
  state (readRegs regs 0 1 source.head?) source [] count

theorem peek_eval (regs : Fin 8 → Bool) (source count : List Bool) :
    Eval peek 1 (state regs source [] count) (ready regs source count) := .base (.atom _ _)

theorem ready_nil (regs : Fin 8 → Bool) (count : List Bool) :
    (ready regs [] count).regs 1 = false := by simp [ readRegs]

theorem ready_cons (regs : Fin 8 → Bool) (bits source count : List Bool) :
    (ready regs (Encoding.frame bits ++ source) count).regs 1 = true := by
  cases bits <;> simp [ readRegs, Encoding.frame]

theorem body_eval (regs : Fin 8 → Bool) (bits source count : List Bool) :
    ∃ regs', Eval body (8 * bits.length + 10)
      (state regs (Encoding.frame bits ++ source) [] count)
      (ready regs' source (true :: count)) := by
  obtain ⟨d1, t1, hs1⟩ := readFrame_eval (0 : Fin 3) 1 (by decide)
    (state regs (Encoding.frame bits ++ source) [] count) bits source rfl rfl
  have hd1 : d1 = state d1.regs source bits.reverse count := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs1]
    funext i
    fin_cases i <;> simp []
  rw [hd1] at t1
  let r2 := readRegs d1.regs 0 1 none
  have t2 : Eval clearPayload (2 * bits.length + 3)
      (state d1.regs source bits.reverse count) (state r2 source [] count) := by
    have hc := TupleProgram.clear_eval (1 : Fin 3) (0 : Fin 8) 1
      (state d1.regs source bits.reverse count)
    have hs : (⟨r2, StackRoutines.clearStacks 1
        (state d1.regs source bits.reverse count).stacks⟩ : StructuredProgram.State 8 3) =
        state r2 source [] count := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext i
      fin_cases i <;> rfl
    change Eval clearPayload (2 * bits.reverse.length + 3)
      (state d1.regs source bits.reverse count)
      (⟨r2, StackRoutines.clearStacks 1
        (state d1.regs source bits.reverse count).stacks⟩ : StructuredProgram.State 8 3) at hc
    rw [hs] at hc
    simpa only [List.length_reverse] using hc
  let r3 := Function.update r2 (0 : Fin 8) true
  have t3 : Eval increment 2 (state r2 source [] count) (state r3 source [] (true :: count)) := by
    have hp := TupleProgram.pushConst_eval (2 : Fin 3) (0 : Fin 8) true
      (state r2 source [] count)
    have hs : TupleProgram.pushedState 2 0 true (state r2 source [] count) =
        state r3 source [] (true :: count) := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext i
      fin_cases i <;> rfl
    rw [hs] at hp
    exact hp
  have t4 := peek_eval r3 source (true :: count)
  refine ⟨r3, ?_⟩
  convert t1.seq (t2.seq (t3.seq t4)) using 1 ; simp [] ; omega

def budget (xs : List (List Bool)) : ℕ :=
  (xs.map fun bits => 8 * bits.length + 11).sum + 1

theorem loop_eval (xs : List (List Bool)) (regs : Fin 8 → Bool) (count : List Bool) :
    ∃ regs', Eval loop (budget xs)
      (ready regs (words xs) count)
      (state regs' [] [] (List.replicate xs.length true ++ count)) := by
  induction xs generalizing regs count with
  | nil =>
    refine ⟨(ready regs [] count).regs, ?_⟩
    simpa [loop, budget, words, ready, state] using
      (Eval.while_false (body := body) (ready_nil regs count))
  | cons bits xs ih =>
    let r0 := (ready regs (words (bits :: xs)) count).regs
    obtain ⟨r1, t1⟩ := body_eval r0 bits (words xs) count
    have ht1 : Eval body (8 * bits.length + 10)
        (ready regs (words (bits :: xs)) count)
        (ready r1 (words xs) (true :: count)) := by
      simpa only [ready, words, r0] using t1
    obtain ⟨rf, t2⟩ := ih r1 (true :: count)
    have ht := Eval.while_true (ready_cons regs bits (words xs) count) ht1 t2
    have hcount : List.replicate xs.length true ++ true :: count =
        List.replicate (bits :: xs).length true ++ count := by
      rw [List.length_cons, List.replicate_add]
      simp [List.append_assoc]
    refine ⟨rf, ?_⟩
    convert ht using 1
    · simp only [budget, List.map_cons, List.sum_cons]
      omega
    · rfl
    · exact congrArg (state rf [] []) hcount.symm

theorem budget_le (xs : List (List Bool)) : budget xs ≤ 11 * (words xs).length + 1 := by
  induction xs with
  | nil => simp [budget, words]
  | cons bits xs ih =>
    simp only [budget, List.map_cons, List.sum_cons] at *
    simp only [words, List.length_append, Encoding.length_frame]
    omega

/-- The counter consumes actual frames and emits one true bit per frame. -/
theorem program_trace (xs : List (List Bool)) (regs : Fin 8 → Bool) (count : List Bool) :
    ∃ n ≤ 11 * (words xs).length + 3, ∃ regs',
      Trace program n
        ((state regs (words xs) [] count).withPC (some program.entry))
        ((state regs' [] [] (List.replicate xs.length true ++ count)).withPC none) := by
  obtain ⟨rf, ht⟩ := loop_eval xs regs count
  refine ⟨1 + budget xs + 1, by have := budget_le xs; omega, rf, ?_⟩
  exact compiled_halt_trace ((peek_eval regs (words xs) count).seq ht) 0 2

end SubexponentialSAT.Subexp.PackingFrameCount

end OAI.Algorithms
