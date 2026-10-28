import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Binary quotient and remainder on caller-selected stack ports

The fixed quotient program is relocated to eight distinct caller ports.  Its
existing instruction-trace bound is retained exactly.  Endpoints are explicit
updates of the caller's own stack store, so every unassigned stack is framed.
-/

namespace SubexponentialSAT.ModularQuotientLift

open BitProgram StackRoutines StructuredCalls
open ModularQuotientPrograms ModularQuotientArithmetic

/-- Only the remainder, consumed input, and quotient ports change. -/
def quotientStacksAt {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update (Function.update stk (ports 0) remainder)
    (ports 6) []) (ports 7) quotient

/-- Relocation changes only the fixed port names, not the instruction table size. -/
abbrev programAt {s : ℕ} (ports : Fin 8 ↪ Fin s) : Program 8 s 92 :=
  ProgramLinking.liftProgram quotientProgram id ports

@[simp] theorem programAt_entry {s : ℕ} (ports : Fin 8 ↪ Fin s) :
    (programAt ports).entry = 0 := rfl

theorem caller_frame {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) (j : Fin s)
    (h0 : j ≠ ports 0) (h6 : j ≠ ports 6) (h7 : j ≠ ports 7) :
    quotientStacksAt ports remainder quotient stk j = stk j := by
  simp [quotientStacksAt, h0, h6, h7]

theorem unassigned_frame {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) (j : Fin s)
    (hj : j ∉ Set.range ports) :
    quotientStacksAt ports remainder quotient stk j = stk j := by
  apply caller_frame
  · intro h; exact hj ⟨0, h.symm⟩
  · intro h; exact hj ⟨6, h.symm⟩
  · intro h; exact hj ⟨7, h.symm⟩

@[simp] theorem quotientStacksAt_remainder {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 0) = remainder := by
  simp [quotientStacksAt, ports.injective.eq_iff]

@[simp] theorem quotientStacksAt_input {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 6) = [] := by
  simp [quotientStacksAt, ports.injective.eq_iff]

@[simp] theorem quotientStacksAt_quotient {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 7) = quotient := by
  simp [quotientStacksAt]

@[simp] theorem quotientStacksAt_modulus {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 5) = stk (ports 5) := by
  simp [quotientStacksAt, ports.injective.eq_iff]

private theorem extend_restrict {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (stk : Stacks (Fin s)) :
    Function.extend ports (fun i => stk (ports i)) stk = stk := by
  classical
  funext j
  by_cases hj : ∃ i, ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact ports.injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hj

private theorem quotientStacks_update (m x remainder quotient : List Bool) :
    Function.update (Function.update (Function.update (quotientStacks [] m x [])
      (0 : Fin 8) remainder) 6 []) 7 quotient =
      quotientStacks remainder m [] quotient := by
  funext i
  fin_cases i <;> simp [quotientStacks]

private theorem extend_result {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (m x remainder quotient : List Bool) (stk : Stacks (Fin s))
    (hlocal : (fun i => stk (ports i)) = quotientStacks [] m x []) :
    Function.extend ports (quotientStacks remainder m [] quotient) stk =
      quotientStacksAt ports remainder quotient stk := by
  rw [← quotientStacks_update m x remainder quotient, ← hlocal]
  simp only [ProgramLinking.extend_update ports.injective, extend_restrict]
  rfl

/-- The actual quotient routine runs within its proved bound on arbitrary
caller storage.  Ports `1` through `4` are initially empty work stacks. -/
theorem programAt_runsIn {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (m x : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin s))
    (h0 : stk (ports 0) = []) (h1 : stk (ports 1) = [])
    (h2 : stk (ports 2) = []) (h3 : stk (ports 3) = [])
    (h4 : stk (ports 4) = []) (h5 : stk (ports 5) = m)
    (h6 : stk (ports 6) = x) (h7 : stk (ports 7) = []) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn (programAt ports) (100 * (m.length + x.length + 1) ^ 2)
        ⟨some (programAt ports).entry, regs, stk⟩
        ⟨none, finalRegs, quotientStacksAt ports (divide m x).2 (divide m x).1 stk⟩ := by
  have hlocal : (fun i => stk (ports i)) = quotientStacks [] m x [] := by
    funext i
    fin_cases i <;> simpa [quotientStacks] using (by assumption)
  have hin : Function.extend ports (quotientStacks [] m x []) stk = stk := by
    rw [← hlocal]
    exact extend_restrict ports stk
  have hout := extend_result ports m x (divide m x).2 (divide m x).1 stk hlocal
  obtain ⟨finalRegs, run⟩ := quotient_correct regs m x
  have lifted := ProgramLinking.liftProgram_runsIn quotientProgram id ports
    (⟨none, regs, stk⟩ : Cfg 8 s 92) Function.injective_id ports.injective run
  refine ⟨finalRegs, ?_⟩
  rw [show (programAt ports).entry = 0 by apply Fin.ext; rfl]
  simpa only [programAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    ProgramLinking.liftProgram, ProgramLinking.extend_id, id_eq, hin, hout] using lifted

/-- A direct structured-call interface, retaining the genuine trace length
rather than padding it to the upper bound. -/
theorem programAt_eval {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (m x : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin s))
    (h0 : stk (ports 0) = []) (h1 : stk (ports 1) = [])
    (h2 : stk (ports 2) = []) (h3 : stk (ports 3) = [])
    (h4 : stk (ports 4) = []) (h5 : stk (ports 5) = m)
    (h6 : stk (ports 6) = x) (h7 : stk (ports 7) = []) :
    ∃ n ≤ 100 * (m.length + x.length + 1) ^ 2, ∃ finalRegs : Fin 8 → Bool,
      Eval (.call (programAt ports)) n ⟨regs, stk⟩
        ⟨finalRegs, quotientStacksAt ports (divide m x).2 (divide m x).1 stk⟩ := by
  obtain ⟨finalRegs, n, hn, trace⟩ :=
    programAt_runsIn ports m x regs stk h0 h1 h2 h3 h4 h5 h6 h7
  exact ⟨n, hn, finalRegs, .call _ trace⟩

/-- The verified binary-machine compiler preserves this arbitrary-frame run. -/
theorem programAt_primitive {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (m x : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin s))
    (h0 : stk (ports 0) = []) (h1 : stk (ports 1) = [])
    (h2 : stk (ports 2) = []) (h3 : stk (ports 3) = [])
    (h4 : stk (ports 4) = []) (h5 : stk (ports 5) = m)
    (h6 : stk (ports 6) = x) (h7 : stk (ports 7) = []) :
    ∃ finalRegs : Fin 8 → Bool,
      Computation.RunsIn (primitive (programAt ports)).step
        (primitiveOverhead (programAt ports) * (100 * (m.length + x.length + 1) ^ 2))
        (primitiveCfg (programAt ports) ⟨some (programAt ports).entry, regs, stk⟩)
        (primitiveCfg (programAt ports)
          ⟨none, finalRegs, quotientStacksAt ports (divide m x).2 (divide m x).1 stk⟩) := by
  obtain ⟨finalRegs, run⟩ := programAt_runsIn ports m x regs stk h0 h1 h2 h3 h4 h5 h6 h7
  exact ⟨finalRegs, BitProgram.primitive_execution _ run⟩

end SubexponentialSAT.ModularQuotientLift

end OAI.Algorithms
