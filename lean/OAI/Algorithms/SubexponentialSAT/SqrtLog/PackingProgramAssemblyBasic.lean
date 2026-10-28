import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialStep

namespace OAI.Algorithms

/-! Concrete stack transport for the combined packing score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 16 48

abbrev move (src dst tmp : Fin 48) : Cmd 16 48 :=
  .seq (.call (transferProgram src tmp 0 1))
    (.call (transferProgram tmp dst 0 1))

def moved (d : Data) (src dst : Fin 48) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src)⟩

/-- Two actual transfers move a whole bit string without reversing it. -/
theorem move_eval (d : Data) (src dst tmp : Fin 48)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hd : d.stacks dst = []) (ht : d.stacks tmp = []) :
    Eval (move src dst tmp) (6*(d.stacks src).length+6) d (moved d src dst) := by
  let a := SubexponentialSAT.SubexpScanPrimitives.afterTransfer d src tmp 0 1
  have h₁ := SubexponentialSAT.SubexpScanPrimitives.transfer_eval d src tmp 0 1 hst (by decide)
  have h₂ := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a tmp dst 0 1 htd (by decide)
  have ha : a.stacks tmp = (d.stacks src).reverse := by
    simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,transferStacks,ht]
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer a tmp dst 0 1 = moved d src dst := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,readRegs_reset]
    · funext j
      by_cases hjs : j=src
      · subst j
        simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,hsd,hst,Ne.symm hsd,Ne.symm htd]
      by_cases hjd : j=dst
      · subst j
        simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,Ne.symm hsd,Ne.symm htd,hd,ht]
      by_cases hjt : j=tmp
      · subst j
        simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,Ne.symm hsd,Ne.symm hst,htd,Ne.symm htd,hd,ht]
      · simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,hjs,hjd,hjt]
  rw [he] at h₂
  have h := h₁.seq h₂
  convert h using 1 ; simp [ha,List.length_reverse] ; omega

/-- Runtime metadata occupies high20..23 at boundaries and spare12..15
while the incidence subroutine uses its own high work bank. -/
def metadata : List (Fin 48 × Fin 48) := [(20,12),(21,13),(22,14),(23,15)]

def moveMany : List (Fin 48 × Fin 48) → Cmd 16 48
  | [] => .base .skip
  | (src,dst)::rest => .seq (move src dst 16) (moveMany rest)

def moveState : List (Fin 48 × Fin 48) → Data → Data
  | [], d => d
  | (src,dst)::rest, d => moveState rest (moved d src dst)

def moveCost : List (Fin 48 × Fin 48) → Data → ℕ
  | [], _ => 0
  | (src,dst)::rest, d => 6*(d.stacks src).length+6 + moveCost rest (moved d src dst)

def MoveReady : List (Fin 48 × Fin 48) → Data → Prop
  | [], _ => True
  | (src,dst)::rest,d => src ≠ dst ∧ src ≠ 16 ∧ (16 : Fin 48) ≠ dst ∧
      d.stacks dst = [] ∧ d.stacks 16 = [] ∧ MoveReady rest (moved d src dst)

theorem moveMany_eval (moves : List (Fin 48 × Fin 48)) (d : Data) (h : MoveReady moves d) :
    Eval (moveMany moves) (moveCost moves d) d (moveState moves d) := by
  induction moves generalizing d with
  | nil => exact .base (.skip d)
  | cons p ps ih =>
    rcases p with ⟨src,dst⟩
    rcases h with ⟨hsd,hst,htd,hd,ht,hr⟩
    exact (move_eval d src dst 16 hsd hst htd hd ht).seq (ih _ hr)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
