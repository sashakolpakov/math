import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeExponentMaster
import OAI.Algorithms.SubexponentialSAT.SubexpIndexWidthProgram

namespace OAI.Algorithms

/-! Generate both retained-key width and the reusable exponent master from D. -/

namespace SubexponentialSAT.SubexpNodeNumericSetup

open BitProgram StructuredCalls

abbrev Data := State 16 256

def registers : Fin 3 → Fin 16 := Fin.castAdd 13
def ports : Fin 5 → Fin 256 := ![0, 1, 109, 92, 4]

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem ports_injective : Function.Injective ports := by decide

abbrev widthCall : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram SubexpIndexWidthProgram.program registers ports)

abbrev width : Cmd 16 256 := .seq (SubexpNodeCacheSetup.clear 92) widthCall

abbrev command : Cmd 16 256 := .seq width SubexpNodeExponentMaster.command

def widthBudget (D : ℕ) (d : Data) : ℕ :=
  2 * (d.stacks 92).length + 3 + SubexpIndexWidthProgram.runtimeBound D

def budget (D : ℕ) (d : Data) : ℕ :=
  widthBudget D d + SubexpNodeExponentMaster.budget D d

theorem width_eval (d : Data) (D : ℕ)
    (hD : d.stacks 109 = List.replicate D true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h4 : d.stacks 4 = []) :
    ∃ n ≤ widthBudget D d, ∃ e : Data, Eval width n d e ∧
      e.stacks = Function.update d.stacks 92
        (List.replicate (SubexpSymbolicCost.indexBits D) true) := by
  let a := SubexpNodeCacheSetup.clearOut d 92
  have hc := SubexpNodeCacheSetup.clear_eval d 92
  obtain ⟨n, e, hn, he, hs, _⟩ := SubexpIndexWidthProgram.lifted_output
    registers ports registers_injective ports_injective D a
    (by simpa [a, SubexpNodeCacheSetup.clearOut, ports, SubexpIndexWidthProgram.unary] using hD)
    (by simpa [a, SubexpNodeCacheSetup.clearOut, ports] using h0)
    (by simpa [a, SubexpNodeCacheSetup.clearOut, ports] using h1)
    (by simp [a, SubexpNodeCacheSetup.clearOut, ports])
    (by simpa [a, SubexpNodeCacheSetup.clearOut, ports] using h4)
  refine ⟨_, Nat.add_le_add_left hn _, e, hc.seq he, ?_⟩
  simpa [a, SubexpNodeCacheSetup.clearOut, ports, SubexpIndexWidthProgram.unary] using hs

theorem command_eval (d : Data) (D : ℕ)
    (hD : d.stacks 109 = List.replicate D true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h4 : d.stacks 4 = [])
    (hwork : ∀ i ∈ SubexpNodeExponentMaster.work, d.stacks i = []) :
    ∃ n ≤ budget D d, ∃ e : Data, Eval command n d e ∧
      e.stacks = Function.update (Function.update d.stacks 92
        (List.replicate (SubexpSymbolicCost.indexBits D) true)) 127
        (Encoding.encodeList id (SubexpOuterJobs.momentRecords D)) := by
  obtain ⟨n, hn, a, ha, hs⟩ := width_eval d D hD h0 h1 h4
  obtain ⟨m, hm, e, he, ht⟩ := SubexpNodeExponentMaster.command_eval a D
    (by simpa [hs] using hD) (by
      intro i hi
      have hi92 : i ≠ 92 := by
        simp only [SubexpNodeExponentMaster.work, List.mem_cons, List.mem_nil_iff,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [hs, hi92] using hwork i hi)
  have hm' : m ≤ SubexpNodeExponentMaster.budget D d := by
    simpa [SubexpNodeExponentMaster.budget, hs] using hm
  refine ⟨n + m, Nat.add_le_add hn hm', e, ha.seq he, ?_⟩
  simpa only [hs, SubexpNodeExponentMaster.output_momentRecords] using ht

abbrev program : Program 16 256 (size command + 1) := compiled command 109 127

theorem program_runs (d : Data) (D : ℕ)
    (hD : d.stacks 109 = List.replicate D true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h4 : d.stacks 4 = [])
    (hwork : ∀ i ∈ SubexpNodeExponentMaster.work, d.stacks i = []) :
    ∃ e : Data, RunsIn program (budget D d + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 92
        (List.replicate (SubexpSymbolicCost.indexBits D) true)) 127
        (Encoding.encodeList id (SubexpOuterJobs.momentRecords D)) := by
  obtain ⟨n, hn, e, he, hs⟩ := command_eval d D hD h0 h1 h4 hwork
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 109 127⟩, hs⟩

end SubexponentialSAT.SubexpNodeNumericSetup

end OAI.Algorithms
