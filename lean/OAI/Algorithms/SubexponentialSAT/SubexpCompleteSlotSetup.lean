import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIndexWidthProgram
import OAI.Algorithms.SubexponentialSAT.SubexpSlotSetup

namespace OAI.Algorithms

/-! Generate the complete retained-key master from the unary dimension alone.
The width is first constructed by the fixed unary multiplication program;
the bounded-degree exponent and U/Z loops then emit the actual key records. -/

namespace SubexponentialSAT.SubexpCompleteSlotSetup

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

def registers : Fin 3 → Fin 16 := Fin.castAdd 13
def ports : Fin 5 → Fin 128 := Fin.castAdd 123

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 3 13
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective 5 123

def widthCall : Code := .call
  (ProgramLinking.liftProgram SubexpIndexWidthProgram.program registers ports)

theorem widthCall_eval (D : ℕ) (d : Data)
    (hD : d.stacks 2 = List.replicate D true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ n e, n ≤ SubexpIndexWidthProgram.runtimeBound D ∧ Eval widthCall n d e ∧
      e.stacks = Function.update d.stacks 3
        (List.replicate (SubexpSymbolicCost.indexBits D) true) := by
  obtain ⟨n, e, hn, he, hs, _⟩ := SubexpIndexWidthProgram.lifted_output
    registers ports registers_injective ports_injective D d hD h0 h1 h3 h4
  exact ⟨n, e, hn, he, hs⟩

def command : Code := .seq widthCall (.call SubexpSlotSetup.program)
def program := compiled command 2 14
def bound (D : ℕ) : ℕ :=
  SubexpIndexWidthProgram.runtimeBound D + SubexpSlotSetup.bound D + 1

theorem command_eval (D : ℕ) (d : Data)
    (hD : d.stacks 2 = List.replicate D true)
    (h1 : d.stacks 1 = []) (h3 : d.stacks 3 = [])
    (hwork : ∀ i ∈ SubexpSlotSetup.work, d.stacks i = []) :
    ∃ n e, n ≤ SubexpIndexWidthProgram.runtimeBound D + SubexpSlotSetup.bound D ∧
      Eval command n d e ∧
      e.stacks = Function.update
        (Function.update d.stacks 3 (List.replicate (SubexpSymbolicCost.indexBits D) true))
        14 (SubexpSlotSetup.output D) := by
  obtain ⟨wn, w, hwn, hw, hws⟩ :=
    widthCall_eval D d hD (hwork 0 (by decide)) h1 h3 (hwork 4 (by decide))
  have hwD : w.stacks 2 = List.replicate D true := by simpa [hws] using hD
  have hwI : w.stacks 3 = List.replicate (SubexpSymbolicCost.indexBits D) true := by simp [hws]
  have hwwork : ∀ i ∈ SubexpSlotSetup.work, w.stacks i = [] := by
    intro i hi
    have hi3 : i ≠ 3 := by
      intro heq
      subst i
      exact (by decide : (3 : Fin 128) ∉ SubexpSlotSetup.work) hi
    simpa [hws, hi3] using hwork i hi
  obtain ⟨e, ⟨sn, hsn, hs⟩, hes⟩ := SubexpSlotSetup.program_runs w D hwD hwI hwwork
  refine ⟨wn + sn, e, Nat.add_le_add hwn hsn, hw.seq (.call _ hs), ?_⟩
  rw [hes, hws]

theorem program_runs (D : ℕ) (d : Data)
    (hD : d.stacks 2 = List.replicate D true)
    (h1 : d.stacks 1 = []) (h3 : d.stacks 3 = [])
    (hwork : ∀ i ∈ SubexpSlotSetup.work, d.stacks i = []) :
    ∃ e : Data, RunsIn program (bound D)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update
        (Function.update d.stacks 3 (List.replicate (SubexpSymbolicCost.indexBits D) true))
        14 (SubexpSlotSetup.output D) := by
  obtain ⟨n, e, hn, he, hs⟩ := command_eval D d hD h1 h3 hwork
  exact ⟨e, ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 2 14⟩, hs⟩

theorem program_primitive (D : ℕ) (d : Data)
    (hD : d.stacks 2 = List.replicate D true)
    (h1 : d.stacks 1 = []) (h3 : d.stacks 3 = [])
    (hwork : ∀ i ∈ SubexpSlotSetup.work, d.stacks i = []) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * bound D)
      (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (e.withPC none)) ∧
      e.stacks = Function.update
        (Function.update d.stacks 3 (List.replicate (SubexpSymbolicCost.indexBits D) true))
        14 (SubexpSlotSetup.output D) := by
  obtain ⟨e, he, hs⟩ := program_runs D d hD h1 h3 hwork
  exact ⟨e, BitProgram.primitive_execution program he, hs⟩

theorem bound_le (D : ℕ) :
    bound D ≤ 100 * (D + 1)^2 + 2 +
      ((3 * D + 1).choose D *
        (25 * (3 * D + 2) + SubexpSlotSetup.callbackBound D + 18 * D + 13) + 17 * D + 29) := by
  have h := SubexpSlotSetup.bound_le D
  unfold bound SubexpIndexWidthProgram.runtimeBound
  omega

end SubexponentialSAT.SubexpCompleteSlotSetup

end OAI.Algorithms
