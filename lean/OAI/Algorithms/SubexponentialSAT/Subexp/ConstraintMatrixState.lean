import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixProgram

namespace OAI.Algorithms

/-! The runtime boundary states of the matrix producer. The index is stored
as unary data in both conventions required by the two fixed subroutines. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixProgram

open BitProgram StructuredCalls MatrixWordEncoding MulticolorTypes

def state (p : ℕ) [Fact p.Prime] (r Q t g : ℕ) (coefficients : List (ZMod p))
    (sideBytes : List (List Bool)) (regs : Fin 18 → Bool) (index : ℕ)
    (joint accumulator rowCount remaining : List Bool) : Data :=
  ⟨regs, fun j =>
    if j = 21 then List.replicate r true else
    if j = 22 then List.replicate Q true else
    if j = 25 then List.replicate (index + 1) true else
    if j = 26 then List.replicate (Q * r) true else
    if j = 29 then modulus p else
    if j = 30 then word p 0 else
    if j = 31 then CoefficientPascalProgram.valueWords p coefficients else
    if j = 32 then List.replicate coefficients.length true else
    if j = 37 then List.replicate t true else
    if j = 50 then accumulator else
    if j = 51 then joint else
    if j = 53 then ProgramEncoding.encodeRecords sideBytes else
    if j = 55 then rowCount else
    if j = 62 then List.replicate g true else
    if j = 63 then List.replicate index true else
    if j = 64 then remaining else []⟩

theorem project_fiber (p : ℕ) [Fact p.Prime] (r Q t g : ℕ) (coefficients : List (ZMod p))
    (sideBytes : List (List Bool)) (regs : Fin 18 → Bool) (index : ℕ)
    (accumulator rowCount remaining : List Bool) :
    projectState fiberRegisters fiberPorts
      (state p r Q t g coefficients sideBytes regs index [] accumulator rowCount remaining) =
      TypeFiberProgram.inputState ⟨r, t, g, Q * r, index⟩ sideBytes (regs ∘ fiberRegisters) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;> rfl

variable {r Q Δ : ℕ}

theorem project_slot (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (anchor : UniversalType r Q Δ) (coefficients : List (ZMod p))
    (sideBytes : List (List Bool)) (regs : Fin 18 → Bool)
    (joint accumulator rowCount remaining : List Bool) :
    projectState slotRegisters slotPorts
      (state p r Q t.val g.val coefficients sideBytes regs i.val joint accumulator rowCount remaining) =
      ConstraintMatrixSlot.state (ConstraintMatrixSlot.context p i t anchor coefficients)
        (regs ∘ slotRegisters) joint (ProgramEncoding.encodeRecords sideBytes) accumulator rowCount := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;> rfl

theorem state_fuel (p : ℕ) [Fact p.Prime] (r Q t g : ℕ) (coefficients : List (ZMod p))
    (sideBytes : List (List Bool)) (regs : Fin 18 → Bool) (index : ℕ)
    (joint accumulator rowCount remaining replacement : List Bool) :
    Function.update
      (state p r Q t g coefficients sideBytes regs index joint accumulator rowCount remaining).stacks
      64 replacement =
      (state p r Q t g coefficients sideBytes regs index joint accumulator rowCount replacement).stacks := by
  funext j
  by_cases hj : j = 64
  · subst j; simp [state]
  · simp [state, hj]

theorem state_joint (p : ℕ) [Fact p.Prime] (r Q t g : ℕ) (coefficients : List (ZMod p))
    (sideBytes : List (List Bool)) (regs : Fin 18 → Bool) (index : ℕ)
    (joint accumulator rowCount remaining replacement : List Bool) :
    Function.update
      (state p r Q t g coefficients sideBytes regs index joint accumulator rowCount remaining).stacks
      51 replacement =
      (state p r Q t g coefficients sideBytes regs index replacement accumulator rowCount remaining).stacks := by
  funext j
  by_cases hj : j = 51
  · subst j; simp [state]
  · simp [state, hj]

theorem initialize_eval (p : ℕ) [Fact p.Prime] (r Q Δ t g : ℕ) (coefficients : List (ZMod p))
    (sideBytes : List (List Bool)) (regs : Fin 18 → Bool) :
    Eval (TupleProgram.pushConst 25 0 true) 2
      (input p r Q Δ t g coefficients sideBytes regs)
      (state p r Q t g coefficients sideBytes (Function.update regs 0 true) 0 [] [] []
        (List.replicate Δ true)) := by
  have h := TupleProgram.pushConst_eval (25 : Fin 65) (0 : Fin 18) true
    (input p r Q Δ t g coefficients sideBytes regs)
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;> rfl

theorem advance_eval (p : ℕ) [Fact p.Prime] (r Q t g : ℕ) (coefficients : List (ZMod p))
    (sideBytes : List (List Bool)) (regs : Fin 18 → Bool) (index : ℕ)
    (joint accumulator rowCount remaining : List Bool) :
    Eval advance 4
      (state p r Q t g coefficients sideBytes regs index joint accumulator rowCount remaining)
      (state p r Q t g coefficients sideBytes (Function.update regs 0 true) (index + 1)
        joint accumulator rowCount remaining) := by
  let a := state p r Q t g coefficients sideBytes regs index joint accumulator rowCount remaining
  let b := TupleProgram.pushedState 25 0 true a
  have h0 := TupleProgram.pushConst_eval (25 : Fin 65) (0 : Fin 18) true a
  have h1 := TupleProgram.pushConst_eval (63 : Fin 65) (0 : Fin 18) true b
  have he : TupleProgram.pushedState 63 0 true b =
      state p r Q t g coefficients sideBytes (Function.update regs 0 true) (index + 1)
        joint accumulator rowCount remaining := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [b, a, state]
    · funext j
      by_cases h25 : j = 25
      · subst j; simp [b, a, state, List.replicate_succ]
      by_cases h63 : j = 63
      · subst j; simp [b, a, state, List.replicate_succ]
      simp [b, a, state, h25, h63]
  rw [he] at h1
  exact h0.seq h1

def emittedPrefix {α : Type*} {n : ℕ} (blocks : Fin n → List α) (k : ℕ) : List α :=
  ((List.ofFn blocks).take k).flatten

@[simp] theorem prefix_zero {α : Type*} {n : ℕ} (blocks : Fin n → List α) : emittedPrefix blocks 0 = [] := by
  simp [emittedPrefix]

@[simp] theorem prefix_all {α : Type*} {n : ℕ} (blocks : Fin n → List α) :
    emittedPrefix blocks n = (List.ofFn blocks).flatten := by
  simp [emittedPrefix, List.take_of_length_le]

theorem prefix_step {α : Type*} {n : ℕ} (blocks : Fin n → List α) (i : Fin n) :
    emittedPrefix blocks (i.val + 1) = emittedPrefix blocks i.val ++ blocks i := by
  have hi : i.val < (List.ofFn blocks).length := by simp
  simp [emittedPrefix, List.take_succ_eq_append_getElem hi]

end SubexponentialSAT.Subexp.ConstraintMatrixProgram

end OAI.Algorithms
