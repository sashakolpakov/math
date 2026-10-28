import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentProgram

namespace OAI.Algorithms

/-! A fixed five-instruction routine copies a forward key for exactly the
number of bits in a unary width counter. Empty input reads as false, so the
same routine truncates long keys and zero-pads short keys. -/

namespace SubexponentialSAT.SubexpKeyPadProgram

open BitProgram SubexpExponentProgram

abbrev program : Program 2 3 5 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 1 0 1 1, .branch 1 2 4, .pop 0 0 1 3, .push 2 0 0, .halt]

def storage (input counter output : List Bool) : Fin 3 → List Bool :=
  ![input, counter, output]

abbrev cfg (pc : Option (Fin 5)) (regs : Fin 2 → Bool)
    (input counter output : List Bool) : Cfg 2 3 5 :=
  ⟨pc, regs, storage input counter output⟩

theorem padTake_step (n : ℕ) (input : List Bool) :
    padTake (n + 1) input = input.head?.getD false :: padTake n input.tail := by
  cases input <;> simp [List.replicate_succ]

theorem round_trace (regs : Fin 2 → Bool) (input counter output : List Bool) :
    Trace program 4 (cfg (some 0) regs input (true :: counter) output)
      (cfg (some 0) (readRegs regs 0 1 input.head?) input.tail counter
        (input.head?.getD false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg, storage,
    readRegs, Function.update_apply]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem exit_trace (regs : Fin 2 → Bool) (input output : List Bool) :
    Trace program 3 (cfg (some 0) regs input [] output)
      (cfg none (readRegs regs 0 1 none) input [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg, storage,
    readRegs, Function.update_apply]

theorem pad_trace (width : ℕ) (regs : Fin 2 → Bool) (input output : List Bool) :
    ∃ finalRegs, Trace program (4 * width + 3)
      (cfg (some 0) regs input (List.replicate width true) output)
      (cfg none finalRegs (input.drop width) [] ((padTake width input).reverse ++ output)) := by
  induction width generalizing regs input output with
  | zero =>
    exact ⟨readRegs regs 0 1 none, by simpa using exit_trace regs input output⟩
  | succ n ih =>
    have h₁ := round_trace regs input (List.replicate n true) output
    obtain ⟨finalRegs, h₂⟩ := ih (readRegs regs 0 1 input.head?) input.tail
      (input.head?.getD false :: output)
    refine ⟨finalRegs, ?_⟩
    have total := h₁.trans h₂
    have hd : input.tail.drop n = input.drop (n + 1) := List.drop_tail
    rw [hd] at total
    rw [padTake_step, List.reverse_cons, List.append_assoc]
    convert total using 1
    · omega
    · rfl
    · simp only [List.singleton_append]

end SubexponentialSAT.SubexpKeyPadProgram

end OAI.Algorithms
