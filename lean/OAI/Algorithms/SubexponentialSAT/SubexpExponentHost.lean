import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentController
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! A fixed-port host call to the actual bounded-degree exponent generator. -/

namespace SubexponentialSAT.SubexpExponentHost

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

def registers : Fin 3 → Fin 16 := Fin.castAdd 13

theorem registers_injective : Function.Injective registers := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 16 => k.val) h)

def localRegs (d : Data) (i : Fin 3) : Bool := d.regs (registers i)

def call (ports : Fin 6 ↪ Fin 128) : Code := .call
  (ProgramLinking.liftProgram SubexpExponentController.program registers ports)

def initial (d : Data) (D N : ℕ) : SubexpExponentController.Data :=
  SubexpExponentController.encoded (localRegs d) (List.replicate D 0) N 0 []

def finalData (regs : Fin 3 → Bool) (D N : ℕ) : SubexpExponentController.Data :=
  SubexpExponentController.encoded regs [] N D
    (Encoding.encodeList SubexpExponentController.momentWord (Algorithm.exponentList D N).reverse)

/-- The only input to the generator is the zero coordinate stack and unary
degree budget. No list of candidate exponents is supplied. -/
theorem call_eval (ports : Fin 6 ↪ Fin 128) (d : Data) (D N : ℕ)
    (h : ∀ i, d.stacks (ports i) = (initial d D N).stacks i) :
    ∃ ticks e regs, ticks ≤ 25 * (D + N + 1) * (D + N).choose D + 5 ∧
      Eval (call ports) ticks d e ∧
      (∀ i, e.stacks (ports i) = (finalData regs D N).stacks i) ∧
      (∀ i, (¬ ∃ j, ports j = i) → e.stacks i = d.stacks i) ∧
      (∀ i, (¬ ∃ j, registers j = i) → e.regs i = d.regs i) := by
  obtain ⟨regs, _, ticks, hticks, ht⟩ :=
    SubexpExponentController.controller_runsIn D N (localRegs d)
  have hbefore : embedState registers ports d (initial d D N) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports.injective
    · intro i; rfl
    · intros; rfl
    · exact h
    · intros; rfl
  have he := eval_call_lifted SubexpExponentController.program registers ports d
    registers_injective ports.injective ht
  change Eval (call ports) ticks (embedState registers ports d (initial d D N))
    (embedState registers ports d (finalData regs D N)) at he
  rw [hbefore] at he
  refine ⟨ticks, embedState registers ports d (finalData regs D N), regs, hticks, he, ?_, ?_, ?_⟩
  · intro i
    exact embedState_stack registers ports d (finalData regs D N) ports.injective i
  · intro i hi
    exact embedState_stack_frame registers ports d (finalData regs D N) i hi
  · intro i hi
    exact embedState_register_frame registers ports d (finalData regs D N) i hi

theorem final_output (regs : Fin 3 → Bool) (D N : ℕ) :
    (finalData regs D N).stacks 3 =
      Encoding.encodeList SubexpExponentController.momentWord (Algorithm.exponentList D N).reverse := rfl

theorem final_work (regs : Fin 3 → Bool) (D N : ℕ) :
    (finalData regs D N).stacks 0 = [] ∧
      (finalData regs D N).stacks 1 = List.replicate N true ∧
      (finalData regs D N).stacks 2 = List.replicate D false ∧
      (finalData regs D N).stacks 4 = [] ∧ (finalData regs D N).stacks 5 = [] := by
  simp [finalData, SubexpExponentController.encoded, SubexpExponentController.state,
    SubexpExponentController.storage6, SubexpExponentSuccessor.digitsCode]

end SubexponentialSAT.SubexpExponentHost

end OAI.Algorithms
