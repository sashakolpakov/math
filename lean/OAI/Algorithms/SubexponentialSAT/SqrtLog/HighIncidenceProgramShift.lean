import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramRestrictionTotal

namespace OAI.Algorithms

/-! Actual original-coordinate high-value vector. The existing merger reads
false from its empty low stream, so no high-ID producer or zero-padding oracle
is required. It consumes the mask and high bits and emits the reversed vector. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev zeroMerge (mask high : List Bool) := merge mask high []

theorem zero_iteration (regs : Fin 4 → Bool) (b x : Bool)
    (mask high out : List Bool) :
    ∃ rf, Eval body 4
      (popped regs (b :: mask) (if b then x :: high else high) [] out)
      (popped rf mask high [] ((if b then x else false) :: out)) := by
  let a := popped regs (b :: mask) (if b then x :: high else high) [] out
  let item : Option Bool := if b then some x else none
  let r := readRegs (readRegs regs 0 1 (some b)) 2 3 item
  refine ⟨r, ?_⟩
  have hp : Eval pushBit 1 (state r mask high [] out)
      (state r mask high [] ((if b then x else false) :: out)) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.push (3 : Fin 4) 2)
      (state r mask high [] out))) using 1
    · rfl
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    fin_cases i <;> cases b <;> simp [r, item, state, readRegs,
 StructuredProgram.Atom.instr,
 execInstr]
  have hl : Eval loadBit 2 a (state r mask high [] out) := by
    cases b with
    | false =>
        apply Eval.ite_false (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 4) 2 3) a)) using 1
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs, StructuredProgram.Atom.instr, execInstr]
    | true =>
        apply Eval.ite_true (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 4) 2 3) a)) using 1
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs, StructuredProgram.Atom.instr, execInstr]
  exact hl.seq (hp.seq (popMask_eval r mask high [] ((if b then x else false) :: out)))

theorem zero_loop_eval (regs : Fin 4 → Bool) (mask high out : List Bool)
    (hh : high.length = highCount mask) :
    ∃ rf, Eval loop (5 * mask.length + 1)
      (popped regs mask high [] out)
      (state rf [] [] [] ((zeroMerge mask high).reverse ++ out)) := by
  induction mask generalizing regs high out with
  | nil =>
      have hhigh : high = [] := List.eq_nil_of_length_eq_zero (by
        simpa [highCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful] using hh)
      subst high
      exact ⟨readRegs regs 0 1 none, Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases b with
      | false =>
          have hh' : high.length = highCount mask := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          obtain ⟨ri, hi⟩ := zero_iteration regs false false mask high out
          obtain ⟨rf, hr⟩ := ih ri high (false :: out) hh'
          refine ⟨rf, ?_⟩
          have h := Eval.while_true (show (popped regs (false :: mask) high [] out).regs 1 = true by rfl) hi hr
          convert h using 1 <;> simp only [loop, zeroMerge, merge, List.length_cons,
            List.headD_nil, List.tail_nil, List.reverse_cons, List.append_assoc,
            List.singleton_append, Nat.mul_add, Nat.mul_one,
            Nat.add_comm, Nat.add_left_comm] ; omega
      | true =>
          cases high with
          | nil => simp [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] at hh
          | cons x high =>
              have hh' : high.length = highCount mask := by
                simpa [highCount, Subexp.PaddedCompletion.trueCount,
                  Subexp.PaddedCompletion.successful] using hh
              obtain ⟨ri, hi⟩ := zero_iteration regs true x mask high out
              obtain ⟨rf, hr⟩ := ih ri high (x :: out) hh'
              refine ⟨rf, ?_⟩
              have h := Eval.while_true (show (popped regs (true :: mask) (x :: high) [] out).regs 1 = true by rfl) hi hr
              convert h using 1 <;> simp only [loop, zeroMerge, merge, List.length_cons,
                List.headD_cons, List.tail_cons, List.reverse_cons, List.append_assoc,
                List.singleton_append, Nat.mul_add, Nat.mul_one,
                Nat.add_comm, Nat.add_left_comm] ; omega

theorem zero_program_runsIn (regs : Fin 4 → Bool) (mask high out : List Bool)
    (hh : high.length = highCount mask) :
    ∃ rf, RunsIn program (5 * mask.length + 3)
      ((state regs mask high [] out).withPC (some program.entry))
      ((state rf [] [] [] ((zeroMerge mask high).reverse ++ out)).withPC none) := by
  obtain ⟨rf, hl⟩ := zero_loop_eval regs mask high out hh
  have he := (popMask_eval regs mask high [] out).seq hl
  refine ⟨rf, 1 + (5 * mask.length + 1) + 1, by omega, ?_⟩
  exact compiled_halt_trace he 0 3

theorem merge_zero_pad (mask high : List Bool) (l : ℕ) :
    merge mask high (List.replicate l false) = zeroMerge mask high := by
  induction mask generalizing high l with
  | nil => rfl
  | cons b mask ih =>
      cases b
      · cases l <;> simp [zeroMerge, merge, ih, List.replicate_succ]
      · simp [zeroMerge, merge, ih]

/-- The emitted vector has exactly the supplied high bits and zero on every
free coordinate. It retains the full original length. -/
theorem zeroMerge_spec (mask high : List Bool) (hh : high.length = highCount mask) :
    (zeroMerge mask high).length = mask.length ∧
    selected true mask (zeroMerge mask high) = high ∧
    selected false mask (zeroMerge mask high) =
      List.replicate (mask.length - highCount mask) false := by
  have hc : highCount mask ≤ mask.length := List.length_filter_le _ _
  have hs : high.length + (List.replicate (mask.length - highCount mask) false).length =
      mask.length := by simp only [List.length_replicate]; omega
  have h := merge_spec mask high (List.replicate (mask.length - highCount mask) false) hh hs
  simpa only [merge_zero_pad] using h

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
