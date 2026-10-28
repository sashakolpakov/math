import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinaryPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev LocalState := State 8 3

def data (regs : Fin 8 → Bool) (acc next : List Bool) : LocalState :=
  ⟨regs, BinaryPrograms.Add.stackState acc next []⟩

abbrev command : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false))) (.call BinaryPrograms.Add.littleEndianProgram)

def program := compiled command 1 0

/-- This adds two binary words with an actual execution of the fixed adder. -/
theorem command_eval (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 1, ∃ regs',
      Eval command n (data regs acc next) (data regs' (BinaryArithmetic.add acc next) []) := by
  let reset := Function.update regs 0 false
  obtain ⟨regs', n, hn, ht⟩ := BinaryPrograms.Add.littleEndian_run reset acc next
  have hs : (StructuredProgram.Atom.set 0 false).eval (data regs acc next) =
      data reset acc next := by
    rfl
  refine ⟨1 + n, by omega, regs', ?_⟩
  apply Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 0 false) _))
  rw [hs]
  apply Eval.call
  have hentry : BinaryPrograms.Add.littleEndianProgram.entry = 0 := rfl
  simpa [data, reset, BinaryArithmetic.add, StructuredProgram.State.withPC, hentry] using ht

theorem program_trace (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 2, ∃ regs',
      Trace program n ((data regs acc next).withPC (some program.entry))
        ((data regs' (BinaryArithmetic.add acc next) []).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := command_eval regs acc next
  exact ⟨n + 1, by omega, regs', compiled_halt_trace ht 1 0⟩

structure Ports (r s : ℕ) where
  register : Fin 8 → Fin r
  stack : Fin 3 → Fin s
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

variable {r s : ℕ}

noncomputable def state (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) : State r s :=
  embedState p.register p.stack frame (data regs acc next)

abbrev invoke (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram program p.register p.stack)

theorem invoke_eval (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 3, ∃ regs',
      Eval (invoke p) n (state p frame regs acc next)
        (state p frame regs' (BinaryArithmetic.add acc next) []) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs acc next
  exact ⟨n, by omega, regs', eval_call_lifted program p.register p.stack frame
    p.register_injective p.stack_injective ht⟩

theorem invoke_value (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 3, ∃ regs' out,
      BinaryArithmetic.toNat out = BinaryArithmetic.toNat acc + BinaryArithmetic.toNat next ∧
      Eval (invoke p) n (state p frame regs acc next) (state p frame regs' out []) := by
  obtain ⟨n, hn, regs', ht⟩ := invoke_eval p frame regs acc next
  exact ⟨n, hn, regs', BinaryArithmetic.add acc next, BinaryArithmetic.toNat_add _ _, ht⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
