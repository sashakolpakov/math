import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyBasic
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInput

namespace OAI.Algorithms

/-! Paid parking of four runtime integer parameters around the incidence scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def parameters (n s M r : List Bool) : Fin 48 → List Bool :=
  fun j => if j=20 then n else if j=21 then s else if j=22 then M else if j=23 then r else []

def environment (old : Fin 48 → List Bool) (n s M r : List Bool) : Fin 48 → List Bool :=
  fun j => if j=20 then n else if j=21 then s else if j=22 then M else if j=23 then r else old j

abbrev park : Cmd 16 48 := moveMany metadata
abbrev unpark : Cmd 16 48 := moveMany (metadata.map Prod.swap)
def parked (d : Data) : Data := moveState metadata d
def unparked (d : Data) : Data := moveState (metadata.map Prod.swap) d

def parameterLength (d : Data) : ℕ :=
  (d.stacks 20).length+(d.stacks 21).length+(d.stacks 22).length+(d.stacks 23).length

def parkReady (d : Data) : Prop := ∀ j : Fin 48, 12 ≤ j.val → j.val ≤ 16 → d.stacks j=[]
def unparkReady (d : Data) : Prop :=
  d.stacks 16=[] ∧ ∀ j : Fin 48, 20 ≤ j.val → j.val ≤ 23 → d.stacks j=[]

theorem park_ready (d : Data) (h : parkReady d) : MoveReady metadata d := by
  have h12 := h 12 (by decide) (by decide)
  have h13 := h 13 (by decide) (by decide)
  have h14 := h 14 (by decide) (by decide)
  have h15 := h 15 (by decide) (by decide)
  have h16 := h 16 (by decide) (by decide)
  simp [metadata,MoveReady,moved,h12,h13,h14,h15,h16]

theorem park_cost (d : Data) : moveCost metadata d = 6*parameterLength d+24 := by
  simp [moveCost,metadata,moved,parameterLength]
  omega

theorem park_eval (d : Data) (h : parkReady d) :
    Eval park (6*parameterLength d+24) d (parked d) := by
  simpa only [park,parked,park_cost] using moveMany_eval metadata d (park_ready d h)

theorem unpark_ready (d : Data) (h : unparkReady d) : MoveReady (metadata.map Prod.swap) d := by
  have h20 := h.2 20 (by decide) (by decide)
  have h21 := h.2 21 (by decide) (by decide)
  have h22 := h.2 22 (by decide) (by decide)
  have h23 := h.2 23 (by decide) (by decide)
  simp [metadata,MoveReady,moved,h20,h21,h22,h23,h.1]

theorem unpark_cost (d : Data) : moveCost (metadata.map Prod.swap) d =
    6*((d.stacks 12).length+(d.stacks 13).length+(d.stacks 14).length+(d.stacks 15).length)+24 := by
  simp [moveCost,metadata,moved]
  omega

theorem unpark_eval (d : Data) (h : unparkReady d) :
    Eval unpark (6*((d.stacks 12).length+(d.stacks 13).length+
      (d.stacks 14).length+(d.stacks 15).length)+24) d (unparked d) := by
  simpa only [unpark,unparked,unpark_cost] using
    moveMany_eval (metadata.map Prod.swap) d (unpark_ready d h)

theorem parked_stack (d : Data) (j : Fin 48) :
    (parked d).stacks j =
      if j=12 then d.stacks 20 else if j=13 then d.stacks 21 else
      if j=14 then d.stacks 22 else if j=15 then d.stacks 23 else
      if j=20 ∨ j=21 ∨ j=22 ∨ j=23 then [] else d.stacks j := by
  fin_cases j <;> simp [parked,moveState,metadata,moved]

theorem unparked_stack (d : Data) (j : Fin 48) :
    (unparked d).stacks j =
      if j=20 then d.stacks 12 else if j=21 then d.stacks 13 else
      if j=22 then d.stacks 14 else if j=23 then d.stacks 15 else
      if j=12 ∨ j=13 ∨ j=14 ∨ j=15 then [] else d.stacks j := by
  fin_cases j <;> simp [unparked,moveState,metadata,moved]

/-- Restoring parameters after a framed scorer also restores every scratch
slot used to park them. The scorer may replace output0 only. -/
theorem unpark_after_output (d e : Data) (h : parkReady d)
    (he : ∀ j, j ≠ 0 → e.stacks j=(parked d).stacks j) :
    (unparked e).stacks = Function.update d.stacks 0 (e.stacks 0) := by
  funext j
  have h12 := h 12 (by decide) (by decide)
  have h13 := h 13 (by decide) (by decide)
  have h14 := h 14 (by decide) (by decide)
  have h15 := h 15 (by decide) (by decide)
  rw [unparked_stack]
  fin_cases j <;> simp [he,parked_stack,h12,h13,h14,h15]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
