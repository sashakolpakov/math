import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendPorts
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Paid copies and fixed constants used between frontend stages. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def copy (src dst : Fin 768) : Code := .call (StackRoutines.copyProgram src dst 679 0 1)
def copied (a : Data) (src dst : Fin 768) := SubexpScanPrimitives.afterCopy a src dst 0 1

def CopyReady (a : Data) (src dst : Fin 768) : Prop :=
  src ≠ dst ∧ src ≠ 679 ∧ (679 : Fin 768) ≠ dst ∧ a.stacks 679 = []

theorem copy_eval (a : Data) (src dst : Fin 768) (h : CopyReady a src dst) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a (copied a src dst) :=
  SubexpScanPrimitives.copy_eval a src dst 679 0 1 h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

@[simp] theorem copied_stack (a : Data) (src dst i : Fin 768) :
    (copied a src dst).stacks i = if i=dst then a.stacks src ++ a.stacks dst else a.stacks i := by
  simp [copied,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,Function.update_apply]

def copies : List (Fin 768 × Fin 768) → Code
  | [] => .base .skip
  | (s,d)::xs => .seq (copy s d) (copies xs)
def copiesState : List (Fin 768 × Fin 768) → Data → Data
  | [],a => a
  | (s,d)::xs,a => copiesState xs (copied a s d)
def copiesCost : List (Fin 768 × Fin 768) → Data → ℕ
  | [],_ => 0
  | (s,d)::xs,a => 7*(a.stacks s).length+5+copiesCost xs (copied a s d)
def CopiesReady : List (Fin 768 × Fin 768) → Data → Prop
  | [],_ => True
  | (s,d)::xs,a => CopyReady a s d ∧ CopiesReady xs (copied a s d)

theorem copies_eval (xs : List (Fin 768 × Fin 768)) (a : Data) (h : CopiesReady xs a) :
    Eval (copies xs) (copiesCost xs a) a (copiesState xs a) := by
  induction xs generalizing a with
  | nil => exact .base (.skip a)
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      exact (copy_eval a s d h.1).seq (ih _ h.2)

theorem copies_frame (xs : List (Fin 768 × Fin 768)) (a : Data) (i : Fin 768)
    (hi : ∀ x ∈ xs, x.2 ≠ i) : (copiesState xs a).stacks i = a.stacks i := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨s,d⟩
      rw [copiesState,ih _ (fun x hx => hi x (List.mem_cons_of_mem _ hx))]
      simp [copied_stack,Ne.symm (hi (s,d) List.mem_cons_self)]

def setRegs (xs : List (StructuredProgram.Atom 40 768)) : Code := .base (SubexpParameterProgram.atoms xs)
def regsState (xs : List (StructuredProgram.Atom 40 768)) (a : Data) := SubexpParameterProgram.runAtoms xs a

theorem setRegs_eval (xs : List (StructuredProgram.Atom 40 768)) (a : Data) :
    Eval (setRegs xs) xs.length a (regsState xs a) :=
  .base (SubexpParameterProgram.atoms_eval xs a)

def clearPrivate : Code := BankRoutines.clearCmd 679 0 1
  ((List.finRange 262).map (block 417 262 (by decide)))

theorem clearPrivate_eq : clearPrivate = BankRoutines.clearCmd 679 (0 : Fin 40) 1
    ((List.finRange 262).map (block 417 262 (by decide))) := rfl

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
