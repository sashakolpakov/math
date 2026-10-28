import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! A fixed finite bit program testing a mask's weight against a unary budget.
Both the mask and the budget are runtime stack data. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram.WeightScan

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 2

def state (regs : Fin 4 → Bool) (bits budget : List Bool) : Data :=
  ⟨regs, ![bits, budget]⟩

abbrev read : Cmd 4 2 := .base (.atom (.pop 0 0 1))
abbrev consume : Cmd 4 2 := .base (.atom (.pop 1 2 3))
abbrev branch : Cmd 4 2 := .ite 0 consume (.base .skip)
abbrev loop : Cmd 4 2 := .while 1 (.seq branch read)
abbrev core : Cmd 4 2 := .seq read loop
abbrev finish : Cmd 4 2 := .base (.atom (.peek 1 2 3))
abbrev command : Cmd 4 2 := .seq core finish

def afterRead (regs : Fin 4 → Bool) (bits : List Bool) : Fin 4 → Bool :=
  readRegs regs 0 1 bits.head?

def afterConsume (regs : Fin 4 → Bool) (budget : List Bool) : Fin 4 → Bool :=
  readRegs regs 2 3 budget.head?

theorem read_eval (regs : Fin 4 → Bool) (bits budget : List Bool) :
    Eval read 1 (state regs bits budget)
      (state (afterRead regs bits) bits.tail budget) := by
  have h : (StructuredProgram.Atom.pop (r := 4) (s := 2) 0 0 1).eval
      (state regs bits budget) = state (afterRead regs bits) bits.tail budget := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state,
        StructuredProgram.Atom.instr, execInstr]
  rw [← h]
  exact .base (.atom _ _)

theorem consume_eval (regs : Fin 4 → Bool) (bits budget : List Bool) :
    Eval consume 1 (state regs bits budget)
      (state (afterConsume regs budget) bits budget.tail) := by
  have h : (StructuredProgram.Atom.pop (r := 4) (s := 2) 1 2 3).eval
      (state regs bits budget) = state (afterConsume regs budget) bits budget.tail := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state,
        StructuredProgram.Atom.instr, execInstr]
  rw [← h]
  exact .base (.atom _ _)

/-- The inner scan consumes one budget token for each true bit, even after
budget exhaustion. No machine instruction computes a population count. -/
theorem core_eval (bits budget : List Bool) (regs : Fin 4 → Bool) :
    ∃ n ≤ 5 * bits.length + 2, ∃ regs', Eval core n
      (state regs bits budget) (state regs' [] (budget.drop (bits.count true))) := by
  induction bits generalizing budget regs with
  | nil =>
      refine ⟨2, by simp, afterRead regs [], ?_⟩
      exact .seq (read_eval regs [] budget) (.while_false (by simp [state, afterRead, readRegs]))
  | cons bit bits ih =>
      let rr := afterRead regs (bit :: bits)
      have ht : (state rr bits budget).regs 1 = true := by simp [state, rr, afterRead, readRegs]
      cases bit with
      | false =>
          obtain ⟨n, hn, final, hrec⟩ := ih budget rr
          cases hrec with
          | @seq _ _ u v a b c hread hloop =>
              have hb : Eval branch 1 (state rr bits budget) (state rr bits budget) :=
                .ite_false (by simp [state, rr, afterRead, readRegs]) (.base (.skip _))
              have he := Eval.seq (read_eval regs (false :: bits) budget)
                (Eval.while_true ht (Eval.seq hb hread) hloop)
              refine ⟨1 + (1 + u + v + 1), ?_, final, ?_⟩
              · simp only [List.length_cons]; omega
              · simpa [core, loop] using he
      | true =>
          obtain ⟨n, hn, final, hrec⟩ := ih budget.tail (afterConsume rr budget)
          cases hrec with
          | @seq _ _ u v a b c hread hloop =>
              have hb : Eval branch 2 (state rr bits budget)
                  (state (afterConsume rr budget) bits budget.tail) :=
                .ite_true (by simp [state, rr, afterRead, readRegs]) (consume_eval rr bits budget)
              have he := Eval.seq (read_eval regs (true :: bits) budget)
                (Eval.while_true ht (Eval.seq hb hread) hloop)
              refine ⟨1 + (2 + u + v + 1), ?_, final, ?_⟩
              · simp only [List.length_cons]; omega
              · simpa [core, loop, List.tail_drop] using he

/-- Actual fixed-code execution; the last register reports strict weight bound. -/
theorem command_eval (bits budget : List Bool) (regs : Fin 4 → Bool) :
    ∃ n ≤ 5 * bits.length + 3, ∃ regs', Eval command n
      (state regs bits budget) (state regs' [] (budget.drop (bits.count true))) ∧
      regs' 3 = decide (bits.count true < budget.length) := by
  obtain ⟨n, hn, middle, hm⟩ := core_eval bits budget regs
  let rem := budget.drop (bits.count true)
  let final := afterConsume middle rem
  have hf : Eval finish 1 (state middle [] rem) (state final [] rem) := by
    have h : (StructuredProgram.Atom.peek (r := 4) (s := 2) 1 2 3).eval
        (state middle [] rem) = state final [] rem := rfl
    rw [← h]
    exact .base (.atom _ _)
  refine ⟨n + 1, by omega, final, Eval.seq hm hf, ?_⟩
  apply Bool.eq_iff_iff.mpr
  simp [final, afterConsume, readRegs, rem]

def program := compiled command 0 0

theorem program_trace (bits budget : List Bool) (regs : Fin 4 → Bool) :
    ∃ n ≤ 5 * bits.length + 4, ∃ regs', Trace program n
      ((state regs bits budget).withPC (some program.entry))
      ((state regs' [] (budget.drop (bits.count true))).withPC none) ∧
      regs' 3 = decide (bits.count true < budget.length) := by
  obtain ⟨n, hn, regs', h, ha⟩ := command_eval bits budget regs
  exact ⟨n + 1, by omega, regs', compiled_halt_trace h 0 0, ha⟩

end SubexponentialSAT.SqrtLog.SupportProgram.WeightScan

end OAI.Algorithms
