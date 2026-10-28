import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowWorkspace

namespace OAI.Algorithms

/-! Actual copies and clears that place the computed vector, selected
positions and source caches into the row emitter's local layout. -/

namespace SubexponentialSAT.Subexp.UniversalRowRearrange

open BitProgram StructuredCalls StackRoutines UniversalRowWorkspace

inductive Action where
  | copy (source : Fin 288) (destination : Fin 49)
  | clear (destination : Fin 49)
  deriving DecidableEq

def Action.Valid : Action → Prop
  | .copy src dst => src ≠ port dst ∧ src ≠ port 15 ∧ port 15 ≠ port dst
  | .clear _ => True

instance (op : Action) : Decidable op.Valid := by cases op <;> unfold Action.Valid <;> infer_instance

def action : Action → Code
  | .copy src dst => .call (copyProgram src (port dst) (port 15) (0 : Fin 16) 1)
  | .clear dst => .call (clearProgram (port dst) (0 : Fin 16) 1)

def actionResult : Action → Data → Data
  | .copy src dst, a => ⟨readRegs a.regs 0 1 none, copyStacks src (port dst) a.stacks⟩
  | .clear dst, a => ⟨readRegs a.regs 0 1 none, clearStacks (port dst) a.stacks⟩

def actionCost : Action → Data → ℕ
  | .copy src _, a => 7 * (a.stacks src).length + 5
  | .clear dst, a => 2 * (a.stacks (port dst)).length + 3

theorem action_eval (op : Action) (a : Data) (hv : op.Valid)
    (ht : a.stacks (port 15) = []) : Eval (action op) (actionCost op a) a (actionResult op a) := by
  cases op with
  | copy src dst =>
      exact TupleProgram.copy_eval src (port dst) (port 15) (0 : Fin 16) 1
        hv.1 hv.2.1 hv.2.2 (by decide) a ht
  | clear dst => exact TupleProgram.clear_eval (port dst) (0 : Fin 16) 1 a

theorem action_temp (op : Action) (a : Data) (hv : op.Valid)
    (ht : a.stacks (port 15) = []) : (actionResult op a).stacks (port 15) = [] := by
  cases op with
  | copy src dst => simp [actionResult, copyStacks, hv.2.2, ht]
  | clear dst =>
      by_cases h : port 15 = port dst <;> simp [actionResult, clearStacks, h, ht]

theorem action_frame (op : Action) (a : Data) (k : Fin 288)
    (hk : ¬ ∃ j, port j = k) : (actionResult op a).stacks k = a.stacks k := by
  cases op with
  | copy src dst =>
      have h : k ≠ port dst := fun h => hk ⟨dst, h.symm⟩
      simp [actionResult, copyStacks, h]
  | clear dst =>
      have h : k ≠ port dst := fun h => hk ⟨dst, h.symm⟩
      simp [actionResult, clearStacks, h]

def sequence : List Action → Code
  | [] => .base .skip
  | op :: os => .seq (action op) (sequence os)

def result : List Action → Data → Data
  | [], a => a
  | op :: os, a => result os (actionResult op a)

def cost : List Action → Data → ℕ
  | [], _ => 0
  | op :: os, a => actionCost op a + cost os (actionResult op a)

theorem sequence_eval (os : List Action) (a : Data)
    (hv : ∀ op ∈ os, op.Valid) (ht : a.stacks (port 15) = []) :
    Eval (sequence os) (cost os a) a (result os a) := by
  induction os generalizing a with
  | nil => exact .base (.skip _)
  | cons op os ih =>
      have hop := hv op (by simp)
      exact (action_eval op a hop ht).seq
        (ih (actionResult op a) (fun x hx => hv x (by simp [hx])) (action_temp op a hop ht))

theorem result_frame (os : List Action) (a : Data) (k : Fin 288)
    (hk : ¬ ∃ j, port j = k) : (result os a).stacks k = a.stacks k := by
  induction os generalizing a with
  | nil => rfl
  | cons op os ih => exact (ih (actionResult op a)).trans (action_frame op a k hk)

def operations : List Action := [
  .copy (port 48) 24, .clear 48,
  .copy (port 45) 28, .clear 45,
  .copy (port 32) 13, .clear 32,
  .copy (port 44) 10, .clear 44,
  .copy (port 47) 3,
  .clear 21, .clear 22, .clear 25, .clear 26, .clear 29, .clear 30, .clear 31, .clear 46,
  .copy (port 47) 29, .clear 47,
  .copy 135 25, .copy 136 26, .copy 137 27, .copy 134 30]

theorem operations_valid : ∀ op ∈ operations, op.Valid := by decide

def command : Code := sequence operations

theorem command_eval (a : Data) (ht : a.stacks (port 15) = []) :
    Eval command (cost operations a) a (result operations a) :=
  sequence_eval operations a operations_valid ht

def Ready (a : Data) : Prop :=
  ∀ j : Fin 49, j ∉ [18, 21, 22, 25, 26, 29, 30, 31, 32, 44, 45, 46, 47, 48] →
    a.stacks (port j) = []

def preparedWord (a : Data) (j : Fin 49) : Word :=
  if j = 3 then a.stacks (port 47)
  else if j = 10 then a.stacks (port 44)
  else if j = 13 then a.stacks (port 32)
  else if j = 18 then a.stacks (port 18)
  else if j = 24 then a.stacks (port 48)
  else if j = 25 then a.stacks 135
  else if j = 26 then a.stacks 136
  else if j = 27 then a.stacks 137
  else if j = 28 then a.stacks (port 45)
  else if j = 29 then a.stacks (port 47)
  else if j = 30 then a.stacks 134 else []

private theorem high_ne_port (n : Fin 288) (hn : 128 ≤ n.val) (k : Fin 49) :
    n ≠ port k := by
  intro h
  have hk := port_lt_cache k
  rw [← h] at hk
  omega

theorem result_stack (a : Data) (ha : Ready a) (j : Fin 49) :
    (result operations a).stacks (port j) =
      if j = 30 then a.stacks 134
      else if j = 27 then a.stacks 137
      else if j = 26 then a.stacks 136
      else if j = 25 then a.stacks 135
      else if j = 47 then []
      else if j = 29 then a.stacks (port 47)
      else if j = 46 then []
      else if j = 31 then []
      else if j = 30 then []
      else if j = 29 then []
      else if j = 26 then []
      else if j = 25 then []
      else if j = 22 then []
      else if j = 21 then []
      else if j = 3 then a.stacks (port 47)
      else if j = 44 then []
      else if j = 10 then a.stacks (port 44)
      else if j = 32 then []
      else if j = 13 then a.stacks (port 32)
      else if j = 45 then []
      else if j = 28 then a.stacks (port 45)
      else if j = 48 then []
      else if j = 24 then a.stacks (port 48)
      else a.stacks (port j) := by
  have h3 := ha 3 (by decide)
  have h10 := ha 10 (by decide)
  have h13 := ha 13 (by decide)
  have h24 := ha 24 (by decide)
  have h27 := ha 27 (by decide)
  have h28 := ha 28 (by decide)
  simp [result, operations, actionResult, copyStacks, clearStacks,
    Function.update_apply, port_injective.eq_iff, high_ne_port 134 (by decide),
    high_ne_port 135 (by decide), high_ne_port 136 (by decide),
    high_ne_port 137 (by decide), h3, h10, h13, h24, h27, h28]

theorem result_prepared (a : Data) (ha : Ready a) (j : Fin 49) :
    (result operations a).stacks (port j) = preparedWord a j := by
  rw [result_stack a ha]
  by_cases h3 : j = 3
  · subst j; simp [preparedWord]
  by_cases h10 : j = 10
  · subst j; simp [preparedWord]
  by_cases h13 : j = 13
  · subst j; simp [preparedWord]
  by_cases h18 : j = 18
  · subst j; simp [preparedWord]
  by_cases h21 : j = 21
  · subst j; simp [preparedWord]
  by_cases h22 : j = 22
  · subst j; simp [preparedWord]
  by_cases h24 : j = 24
  · subst j; simp [preparedWord]
  by_cases h25 : j = 25
  · subst j; simp [preparedWord]
  by_cases h26 : j = 26
  · subst j; simp [preparedWord]
  by_cases h27 : j = 27
  · subst j; simp [preparedWord]
  by_cases h28 : j = 28
  · subst j; simp [preparedWord]
  by_cases h29 : j = 29
  · subst j; simp [preparedWord]
  by_cases h30 : j = 30
  · subst j; simp [preparedWord]
  by_cases h31 : j = 31
  · subst j; simp [preparedWord]
  by_cases h32 : j = 32
  · subst j; simp [preparedWord]
  by_cases h44 : j = 44
  · subst j; simp [preparedWord]
  by_cases h45 : j = 45
  · subst j; simp [preparedWord]
  by_cases h46 : j = 46
  · subst j; simp [preparedWord]
  by_cases h47 : j = 47
  · subst j; simp [preparedWord]
  by_cases h48 : j = 48
  · subst j; simp [preparedWord]
  have he := ha j (by simp_all)
  simp [preparedWord, h3, h10, h13, h18, h21, h22, h24, h25, h26,
    h27, h28, h29, h30, h31, h32, h44, h45, h46, h47, h48, he]
theorem command_prepared (a : Data) (ha : Ready a) :
    Eval command (cost operations a) a (result operations a) ∧
      (∀ j : Fin 49, (result operations a).stacks (port j) = preparedWord a j) ∧
      (∀ j : Fin 288, (¬ ∃ k, port k = j) → (result operations a).stacks j = a.stacks j) :=
  ⟨command_eval a (ha 15 (by decide)),
    result_prepared a ha,
    result_frame operations a⟩

end SubexponentialSAT.Subexp.UniversalRowRearrange

end OAI.Algorithms
