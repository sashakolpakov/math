import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RankAssignmentProgram

namespace OAI.Algorithms

/-! Direct caller-state interface for the preserving rank-padding program. -/

namespace SubexponentialSAT.RankAssignmentLift

open BitProgram StackRoutines StructuredCalls RankAssignmentProgram

private theorem extend_restrict {s : ℕ} (ports : Fin 6 ↪ Fin s) (stk : Stacks (Fin s)) :
    Function.extend ports (fun i => stk (ports i)) stk = stk := by
  classical
  funext j
  by_cases hj : ∃ i, ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact ports.injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hj

abbrev programAt {s : ℕ} (ports : Fin 6 ↪ Fin s) : Program 8 s 26 :=
  ProgramLinking.liftProgram RankAssignmentProgram.program id ports

/-- Only the caller's designated output stack changes. The other assigned and
unassigned stacks are both framed, without an opaque state-embedding endpoint. -/
theorem programAt_trace {s : ℕ} (ports : Fin 6 ↪ Fin s)
    (rank shape : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin s))
    (hrank : stk (ports 0) = rank) (hshape : stk (ports 1) = shape)
    (hlen : rank.length ≤ shape.length) (ho : stk (ports 2) = [])
    (hc : stk (ports 3) = []) (ht : stk (ports 4) = []) (hb : stk (ports 5) = []) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace (programAt ports) (7 * rank.length + 14 * shape.length + 17)
        ⟨some (programAt ports).entry, regs, stk⟩
        ⟨none, finalRegs, Function.update stk (ports 2) (ModularArithmetic.padTo shape rank)⟩ ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨finalRegs, trace, hreg⟩ := RankAssignmentProgram.program_trace rank shape regs
    (fun i => stk (ports i)) hrank hshape hlen ho hc ht hb
  have lifted := ProgramLinking.liftProgram_trace RankAssignmentProgram.program id ports
    (⟨none, regs, stk⟩ : Cfg 8 s 26) Function.injective_id ports.injective trace
  have hu := ProgramLinking.extend_update ports.injective (fun i => stk (ports i)) stk
    (2 : Fin 6) (ModularArithmetic.padTo shape rank)
  refine ⟨finalRegs, ?_, hreg⟩
  simpa [programAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    ProgramLinking.liftProgram, hu, extend_restrict] using lifted

theorem programAt_eval {s : ℕ} (ports : Fin 6 ↪ Fin s)
    (rank shape : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin s))
    (hrank : stk (ports 0) = rank) (hshape : stk (ports 1) = shape)
    (hlen : rank.length ≤ shape.length) (ho : stk (ports 2) = [])
    (hc : stk (ports 3) = []) (ht : stk (ports 4) = []) (hb : stk (ports 5) = []) :
    ∃ finalRegs : Fin 8 → Bool,
      Eval (.call (programAt ports)) (7 * rank.length + 14 * shape.length + 17)
        ⟨regs, stk⟩
        ⟨finalRegs, Function.update stk (ports 2) (ModularArithmetic.padTo shape rank)⟩ ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨finalRegs, trace, hreg⟩ := programAt_trace ports rank shape regs stk
    hrank hshape hlen ho hc ht hb
  exact ⟨finalRegs, .call _ trace, hreg⟩

theorem caller_frame {s : ℕ} (ports : Fin 6 ↪ Fin s) (rank shape : List Bool)
    (stk : Stacks (Fin s)) (j : Fin s) (hj : j ≠ ports 2) :
    Function.update stk (ports 2) (ModularArithmetic.padTo shape rank) j = stk j := by
  simp [hj]

end SubexponentialSAT.RankAssignmentLift

end OAI.Algorithms
