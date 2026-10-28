import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyProgram
import OAI.Algorithms.SubexponentialSAT.ExecWorklistLoop

namespace OAI.Algorithms

/-!
# A canonical search input for each worklist head

The worklist occupies the first five stacks. The concrete node search is
shifted past those stacks, and the bounded head reader writes only the copied
formula into that search block. Consequently its projected input depends on
the head formula and the fixed ambient frame, but not on either worklist tail.

The equality holds for every ambient frame. In particular it applies when
registers are initially false, transient stacks 5 through 36 are empty, and
the persistent parameter stacks have arbitrary fixed contents.
-/

namespace SubexponentialSAT.ExecSparsifyCanonicalHead

open BitProgram StructuredCalls
open ExecSparsifyNode (Data headLoaded)

def coreReg : Fin 4 → Fin 32 := Fin.castAdd 28

def coreStack (k : ℕ) (i : Fin 5) : Fin (k + 39) :=
  ⟨i.val, by omega⟩

theorem coreReg_injective : Function.Injective coreReg :=
  Fin.castAdd_injective 4 28

theorem coreStack_injective (k : ℕ) : Function.Injective (coreStack k) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (k + 39) => x.val) h

variable {α : Type*} {k : ℕ}

noncomputable def input (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves : List α) (visits : ℕ) : Data k :=
  ExecWorklistLoop.Ambient.liftData coreReg (coreStack k) frame
    (ExecWorklistLoop.loopData enc ⟨F :: pending, leaves, visits⟩)

/-- Both inputs have a nonempty pending stream, so their loop-register
values are identical even before the head reader runs. -/
theorem input_regs_eq (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves pending' leaves' : List α) (visits visits' : ℕ) :
    (input enc frame F pending leaves visits).regs =
      (input enc frame F pending' leaves' visits').regs := rfl

/-- Every stack beyond the worklist's five ports retains its frame data. -/
theorem input_stack_frame (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves : List α) (visits : ℕ) (i : Fin (k + 39)) (hi : 5 ≤ i.val) :
    (input enc frame F pending leaves visits).stacks i = frame.stacks i := by
  apply embedState_stack_frame coreReg (coreStack k) frame _ i
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem input_search_stack (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves : List α) (visits : ℕ) (i : Fin (k + 34)) :
    (input enc frame F pending leaves visits).stacks (ExecSparsifyProgram.searchPort k i) =
      frame.stacks (ExecSparsifyProgram.searchPort k i) := by
  apply input_stack_frame
  change 5 ≤ 5 + i.val
  omega

/-- The actual post-readHead search projection is independent of both
unbounded tails and the mathematical visit counter. -/
theorem projected_heads_eq (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves pending' leaves' : List α) (visits visits' : ℕ) :
    projectState id (ExecSparsifyProgram.searchPort k)
        (headLoaded (enc F) (input enc frame F pending leaves visits)) =
      projectState id (ExecSparsifyProgram.searchPort k)
        (headLoaded (enc F) (input enc frame F pending' leaves' visits')) := by
  apply congrArg₂ StructuredProgram.State.mk
  · change readRegs (input enc frame F pending leaves visits).regs 0 1 none =
      readRegs (input enc frame F pending' leaves' visits').regs 0 1 none
    rw [input_regs_eq enc frame F pending leaves pending' leaves' visits visits']
  · funext i
    change Function.update (input enc frame F pending leaves visits).stacks
        (ExecSparsifyNode.port k 21) (enc F) (ExecSparsifyProgram.searchPort k i) =
      Function.update (input enc frame F pending' leaves' visits').stacks
        (ExecSparsifyNode.port k 21) (enc F) (ExecSparsifyProgram.searchPort k i)
    by_cases hi : ExecSparsifyProgram.searchPort k i = ExecSparsifyNode.port k 21
    · have hl :
          Function.update (input enc frame F pending leaves visits).stacks
            (ExecSparsifyNode.port k 21) (enc F)
            (ExecSparsifyProgram.searchPort k i) = enc F :=
        (congrArg
          (Function.update (input enc frame F pending leaves visits).stacks
            (ExecSparsifyNode.port k 21) (enc F)) hi).trans
          (Function.update_self (ExecSparsifyNode.port k 21) (enc F)
            (input enc frame F pending leaves visits).stacks)
      have hr :
          Function.update (input enc frame F pending' leaves' visits').stacks
            (ExecSparsifyNode.port k 21) (enc F)
            (ExecSparsifyProgram.searchPort k i) = enc F :=
        (congrArg
          (Function.update (input enc frame F pending' leaves' visits').stacks
            (ExecSparsifyNode.port k 21) (enc F)) hi).trans
          (Function.update_self (ExecSparsifyNode.port k 21) (enc F)
            (input enc frame F pending' leaves' visits').stacks)
      exact hl.trans hr.symm
    · simp only [Function.update_of_ne hi, input_search_stack]

/-- Choose the empty-tail input once per formula. Every reachable occurrence
of that same formula has exactly this projected search state. -/
theorem projected_head_eq (enc : α → List Bool) (frame : Data k) (F : α)
    (pending leaves : List α) (visits : ℕ) :
    projectState id (ExecSparsifyProgram.searchPort k)
        (headLoaded (enc F) (input enc frame F pending leaves visits)) =
      projectState id (ExecSparsifyProgram.searchPort k)
        (headLoaded (enc F) (input enc frame F [] [] 0)) :=
  projected_heads_eq enc frame F pending leaves [] [] visits 0

end SubexponentialSAT.ExecSparsifyCanonicalHead

end OAI.Algorithms
