import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawIDTransportCore
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram

namespace OAI.Algorithms

/-! Fixed Main port injection and physical clean-output relocation for the
raw-ID transport. These finite routines are independent of the parser proof
and are reused by the final closed transport adapter. -/

namespace SubexponentialSAT.SubexpMainRawIDTransport

open BitProgram StructuredCalls SubexpMainProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def ordinary (es : ℕ) (i : Fin 24) : Fin (totalStacks es) :=
  ⟨i.val, by have := i.isLt; dsimp [totalStacks, workStacks]; omega⟩

def stackMap (es : ℕ) (i : Fin 24) : Fin (totalStacks es) :=
  if i = 23 then persistent es 0 else ordinary es i

@[simp] theorem stackMap_raw (es : ℕ) : stackMap es 23 = persistent es 0 := rfl
@[simp] theorem stackMap_output (es : ℕ) : stackMap es 8 = ordinary es 8 := rfl

theorem stackMap_injective (es : ℕ) : Function.Injective (stackMap es) := by
  intro i j h
  have hv := congrArg Fin.val h
  by_cases hi : i = 23 <;> by_cases hj : j = 23
  · exact hi.trans hj.symm
  · simp only [stackMap, persistent, ordinary, hi, hj] at hv
    have := j.isLt
    dsimp [workStacks] at hv
    omega
  · simp only [stackMap, persistent, ordinary, hi, hj] at hv
    have := i.isLt
    dsimp [workStacks] at hv
    omega
  · apply Fin.ext
    simpa only [stackMap, ite_eq_right hi, ite_eq_right hj, ordinary] using hv

def moveOutput (er es : ℕ) : MainCmd er es :=
  SubexpRawIDTransport.moveWord (ordinary es 8) (persistent es 0) (ordinary es 1)
    (scratchValue er) (scratchPresent er)

theorem moveWord_ioState {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (word : List Bool) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hvp : value ≠ present) :
    Eval (SubexpRawIDTransport.moveWord src dst tmp value present)
      (9 * word.length + 8) (StructuredProgram.ioState src word)
      (StructuredProgram.ioState dst word) := by
  have he := SubexpRawIDTransport.moveWord_eval src dst tmp value present
    (StructuredProgram.ioState src word) hsd hst htd hvp
    (by simp [ Ne.symm hst])
  have hs : (StructuredProgram.ioState src word : StructuredProgram.State r s).stacks src = word :=
    by simp []
  have hd : (StructuredProgram.ioState src word : StructuredProgram.State r s).stacks dst = [] :=
    by simp [ Ne.symm hsd]
  rw [hs, hd] at he
  have hend : (⟨readRegs (fun _ => false) value present none,
      Function.update (Function.update (fun i => if i = src then word else []) dst
        (word ++ [])) src []⟩ : StructuredProgram.State r s) =
      StructuredProgram.ioState dst word := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      simp [readRegs, Function.update_apply]
    · funext i
      by_cases hi : i = src
      · subst i
        simp [ hsd]
      · simp [ Function.update_apply, hi]
  change Eval _ _ _ (⟨readRegs (fun _ => false) value present none,
    Function.update (Function.update (fun i => if i = src then word else []) dst
      (word ++ [])) src []⟩ : StructuredProgram.State r s) at he
  rw [hend] at he
  exact he

theorem moveOutput_eval (er es : ℕ) (output : List Bool) :
    Eval (moveOutput er es) (9 * output.length + 8)
      (StructuredProgram.ioState (ordinary es 8) output)
      (initialData er es output) := by
  apply moveWord_ioState
  · intro h
    have hv := congrArg Fin.val h
    change (8 : ℕ) = workStacks es at hv
    dsimp [workStacks] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change (8 : ℕ) = 1 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change (1 : ℕ) = workStacks es at hv
    dsimp [workStacks] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change (0 : ℕ) = 1 at hv
    omega

end SubexponentialSAT.SubexpMainRawIDTransport

end OAI.Algorithms
