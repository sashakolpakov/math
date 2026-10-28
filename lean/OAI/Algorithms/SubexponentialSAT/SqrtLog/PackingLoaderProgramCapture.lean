import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramFrame
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputState

namespace OAI.Algorithms

/-! Consume the incidence installer's transient metadata while preserving an
explicit raw-scope master outside the selector's48-stack bank. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def rawLocal (regs : Fin 16 → Bool) (scopes : List Bool) (n k f : ℕ)
    (pairs : List Bool) : State 16 48 :=
  ⟨regs,fun i => if i=32 then scopes else if i=33 then List.replicate n true
    else if i=34 then List.replicate k true else if i=35 then List.replicate f true
    else if i=45 then pairs else []⟩
noncomputable def rawInput (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List Bool) (n k f : ℕ) (pairs : List Bool) : Data :=
  framed outside (rawLocal regs scopes n k f pairs)

def captureCopies : List (Fin 64 × Fin 64) := [(32,60),(33,4),(35,5)]
def captureClears : List (Fin 64) := [32,33,34,35]
def capture : Code := .seq (copyMany 31 captureCopies) (clearMany captureClears)
def captureBudget (scopeBits n k f : ℕ) := 9*scopeBits+9*n+2*k+9*f+27

/- The full ambient count is retained; the factor prefix never uses the
free-variable count. Scopes are physically copied to master60 before cleanup. -/
theorem capture_eval (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List Bool) (n k f : ℕ) (pairs : List Bool) (h60 : outside 60=[]) :
    ∃ rf, Eval capture (captureBudget scopes.length n k f)
      (rawInput outside regs scopes n k f pairs)
      (framed (Function.update outside 60 scopes)
        (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState rf 0 0 0 n f pairs)) := by
  let a := rawInput outside regs scopes n k f pairs
  let b := copyManyState captureCopies a
  let e := clearManyState captureClears b
  have h31 : a.stacks 31=[] := by simp [a,rawInput,framed_stack,rawLocal]
  have h1 := copyMany_eval 31 captureCopies a (by
    intro p hp; simp [captureCopies] at hp; rcases hp with rfl | rfl | rfl <;> decide) h31
  have h2 := clearMany_eval captureClears b
  have he : e=framed (Function.update outside 60 scopes)
      (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState e.regs 0 0 0 n f pairs) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
    · funext i
      fin_cases i <;> simp [e,b,a,captureClears,captureCopies,clearManyState,clearState,
        copyManyState,copyState,StackRoutines.copyStacks,rawInput,framed_stack,rawLocal,
        SubexponentialSAT.Subexp.AssignmentInputProgram.inputState,h60]
  have hcost : copyManyCost captureCopies a+clearManyCost captureClears b=
      captureBudget scopes.length n k f := by
    simp [captureBudget,captureCopies,captureClears,copyManyCost,clearManyCost,b,a,
      copyManyState,copyState,StackRoutines.copyStacks,clearState,
      rawInput,framed_stack,rawLocal,h60]
    omega
  have h := h1.seq h2
  change Eval capture _ a e at h
  rw [hcost,he] at h
  exact ⟨e.regs,h⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
