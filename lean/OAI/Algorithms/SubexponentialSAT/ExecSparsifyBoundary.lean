import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyCanonicalHead
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyStart

namespace OAI.Algorithms

/-!
# The exact worklist boundary of the concrete node program

The frame contains only persistent parameter words.  The two unbounded
worklist streams occupy their five separate core ports; their values never
appear in a local copying or cleanup bound.
-/

namespace SubexponentialSAT.ExecSparsifyBoundary

open BitProgram StructuredCalls ExecSparsifyNode
open ExecSparsifyCanonicalHead

/-- The actual startup reset and empty workspace establish this frame. -/
def FrameReady {k : ℕ} (frame : Data k) : Prop :=
  (∀ i, frame.regs i = false) ∧
  ∀ i, 5 ≤ i.val → i.val < 37 → frame.stacks i = []

variable {α : Type*} {k : ℕ}

theorem coreStack_eq (i : Fin 5) :
    coreStack k i = port k (Fin.castAdd 34 i) := rfl

theorem input_core (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves : List α) (visits : ℕ) (i : Fin 5) :
    (input enc frame F pending leaves visits).stacks (coreStack k i) =
      (ExecWorklistLoop.loopData enc ⟨F :: pending, leaves, visits⟩).stacks i :=
  embedState_stack coreReg (coreStack k) frame _ (coreStack_injective k) i

@[simp] theorem input_pending (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves : List α) (visits : ℕ) :
    (input enc frame F pending leaves visits).stacks (port k 0) =
      Encoding.encodeList enc (F :: pending) :=
  input_core enc frame F pending leaves visits 0

@[simp] theorem input_leaves (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves : List α) (visits : ℕ) :
    (input enc frame F pending leaves visits).stacks (port k 1) =
      Encoding.encodeList enc leaves :=
  input_core enc frame F pending leaves visits 1

theorem input_clean (enc : α → List Bool) (frame : Data k) (hframe : FrameReady frame)
    (F : α) (pending leaves : List α) (visits : ℕ) :
    ExecSparsifyProgram.CleanEntry (input enc frame F pending leaves visits) := by
  intro i h2 h37
  by_cases hi : i.val < 5
  · let j : Fin 5 := ⟨i.val, hi⟩
    have he : coreStack k j = i := Fin.ext rfl
    rw [← he, input_core]
    have hj : 2 ≤ j.val := h2
    have hclean : ∀ q : Fin 5, 2 ≤ q.val →
        (ExecWorklistLoop.loopData enc ⟨F :: pending, leaves, visits⟩).stacks q = [] := by
      intro q hq
      fin_cases q <;> simp_all []
    exact hclean j hj
  · rw [input_stack_frame enc frame F pending leaves visits i (by omega)]
    exact hframe.2 i (by omega) h37

/-- A finite set of core outputs and the restored frame determine the exact
state required by the generic encoded worklist loop. -/
theorem output_eq (enc : α → List Bool) (frame q : Data k)
    (F : α) (pending leaves : List α) (result : Option (α × α))
    (hframe : FrameReady frame)
    (hr : ∀ i, q.regs i = if i = (2 : Fin 32) then result.isNone else false)
    (hc : ∀ i : Fin 5, q.stacks (coreStack k i) =
      (ExecWorklistLoop.splitData enc F pending leaves result).stacks i)
    (hclean : ∀ i, 5 ≤ i.val → i.val < 37 → q.stacks i = [])
    (hp : ∀ i, 37 ≤ i.val → q.stacks i = frame.stacks i) :
    q = ExecWorklistLoop.Ambient.liftData coreReg (coreStack k) frame
      (ExecWorklistLoop.splitData enc F pending leaves result) := by
  symm
  apply embedState_eq_of_ports coreReg (coreStack k) frame q _
    coreReg_injective (coreStack_injective k)
  · intro i
    rw [hr]
    cases result with
    | none => fin_cases i <;> simp [ coreReg]
    | some pair =>
      rcases pair with ⟨left, right⟩
      fin_cases i <;> simp [ coreReg]
  · intro i hi
    have hne : i ≠ (2 : Fin 32) := by
      intro he
      subst i
      exact hi ⟨2, rfl⟩
    rw [hr, ite_eq_right hne, hframe.1]
  · exact hc
  · intro i hi
    have h5 : 5 ≤ i.val := by
      by_contra h
      exact hi ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    by_cases h37 : i.val < 37
    · rw [hclean i h5 h37, hframe.2 i h5 h37]
    · exact hp i (by omega)

end SubexponentialSAT.ExecSparsifyBoundary

end OAI.Algorithms
