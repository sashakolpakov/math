import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientCheckerLoops

namespace OAI.Algorithms

/-! Full finite-machine execution of the normalized-coefficient checker. -/

namespace SubexponentialSAT.Subexp.CoefficientCheckerProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding
open CoefficientCheckerSemantics

variable (p : ℕ) [Fact p.Prime]

def accepted (A : ℕ) (xs : List (ZMod p)) : Bool :=
  checkHeads xs.length (advanceParity A false) (CoefficientDynamics.shifts A xs)

def outputState (A : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool) : Data :=
  ready p regs false (advanceParity xs.length (advanceParity A false)) (accepted p A xs)
    (CoefficientDynamics.shifts xs.length (CoefficientDynamics.shifts A xs)) [] []

def checkerBudget (A R B : ℕ) : ℕ :=
  A * (shiftBudget R B + 3) + R * checkStepBudget R B + 7 * R + 12

theorem set_negative_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) :
    Eval (.base (.atom (.set 9 false))) 1 (ready p regs g neg ok xs a c)
      (ready p regs g false ok xs a c) := by
  have h : (StructuredProgram.Atom.set 9 false).eval (ready p regs g neg ok xs a c) =
      ready p regs g false ok xs a c := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        ready, wide, lowData, MatrixScalarProgram.state]
    · rfl
  rw [← h]
  exact .base (.atom _ _)

theorem set_accepted_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) :
    Eval (.base (.atom (.set 10 true))) 1 (ready p regs g neg ok xs a c)
      (ready p regs g neg true xs a c) := by
  have h : (StructuredProgram.Atom.set 10 true).eval (ready p regs g neg ok xs a c) =
      ready p regs g neg true xs a c := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        ready, wide, lowData, MatrixScalarProgram.state]
    · rfl
  rw [← h]
  exact .base (.atom _ _)

theorem command_eval (A : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool)
    (g neg ok : Bool) :
    ∃ n, n + 1 ≤ checkerBudget A xs.length (width p) ∧ ∃ regs',
      Eval command n (ready p regs g neg ok xs (List.replicate A true) [])
        (outputState p A xs regs') := by
  have e₁ := set_negative_eval p regs g neg ok xs (List.replicate A true) []
  have e₂ := set_accepted_eval p regs g false ok xs (List.replicate A true) []
  obtain ⟨na, ha, ra, ea⟩ := advance_eval p A regs g false true xs []
  obtain ⟨nc, hc, rc, ec⟩ := checkConsecutive_eval p ra false (advanceParity A false) true
    (CoefficientDynamics.shifts A xs) []
  simp only [CoefficientDynamics.shifts_length] at hc ec
  have he := e₁.seq (e₂.seq (ea.seq ec))
  refine ⟨1 + (1 + (na + nc)), ?_, rc, ?_⟩
  · dsimp [checkerBudget]
    omega
  · simpa only [command, outputState, accepted, Bool.true_and] using he

/-- One fixed instruction table decides the finite normalized coefficient
conditions. Its runtime includes its final halt instruction. -/
theorem program_run (A : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool)
    (g neg ok : Bool) :
    ∃ regs', RunsIn program (checkerBudget A xs.length (width p))
      ((ready p regs g neg ok xs (List.replicate A true) []).withPC (some program.entry))
      ((outputState p A xs regs').withPC none) := by
  obtain ⟨n, hn, r, he⟩ := command_eval p A xs regs g neg ok
  exact ⟨r, n + 1, hn, compiled_halt_trace he 12 12⟩

@[simp] theorem outputState_answer (A : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool) :
    (outputState p A xs regs).regs 10 = accepted p A xs := rfl

theorem accepted_iff (A : ℕ) (xs : List (ZMod p)) :
    accepted p A xs = true ↔
      ∀ d < xs.length, CoefficientDynamics.evaluate xs (A + d) = (-1 : ZMod p)^(A + d) :=
  checkHeads_normalized A xs.length xs

/-- This polynomial is a coarse bound on the actual trace above, not an
independent runtime assumption. -/
theorem checkerBudget_le (A R B : ℕ) :
    checkerBudget A R B ≤ 100000 * (A + R + 1) * (R + 1) * (B + 1)^2 := by
  dsimp [checkerBudget, shiftBudget, checkStepBudget, compareBudget,
    CoefficientPascalProgram.budget, CoefficientPascalProgram.setupBudget,
    CoefficientPascalProgram.rowBudget]
  ring_nf
  omega

theorem primitive_run (A : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool)
    (g neg ok : Bool) :
    ∃ regs', Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (100000 * (A + xs.length + 1) *
        (xs.length + 1) * (width p + 1)^2))
      (primitiveCfg program
        ((ready p regs g neg ok xs (List.replicate A true) []).withPC (some program.entry)))
      (primitiveCfg program ((outputState p A xs regs').withPC none)) := by
  obtain ⟨r, hr⟩ := program_run p A xs regs g neg ok
  exact ⟨r, primitive_execution program (hr.mono (checkerBudget_le A xs.length (width p)))⟩

end SubexponentialSAT.Subexp.CoefficientCheckerProgram

end OAI.Algorithms
