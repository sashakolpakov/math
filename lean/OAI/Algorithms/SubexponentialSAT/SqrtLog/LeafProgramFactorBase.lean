import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramArithmeticNative
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def copy (src dst : Fin 768) : Code :=
  .call (StackRoutines.copyProgram src dst 159 0 1)
def clear (src : Fin 768) : Code :=
  .call (StackRoutines.clearProgram src 0 1)
def move (src dst : Fin 768) : Code := .seq (copy src dst) (clear src)

def nativeRegisters (i : Fin 8) : Fin 40 := i.castAdd 32
def nativeStacks (i : Fin 96) : Fin 768 := i.castAdd 672

def multiply : Code := .call (ProgramLinking.liftProgram
  (compiled (HashCircuitProgram.Native.productAdapter HashCircuitProgram.Native.product) 61 67)
    nativeRegisters nativeStacks)

/-- The running head-local product is parked on151 while the next factor is
computed on67. Native multiplication consumes61 and returns67. -/
def accumulate : Code := .seq (move 67 61)
  (.seq (move 151 67) (.seq multiply (move 67 151)))


theorem nativeRegisters_injective : Function.Injective nativeRegisters :=
  Fin.castAdd_injective 8 32
theorem nativeStacks_injective : Function.Injective nativeStacks :=
  Fin.castAdd_injective 96 672

/-- Movement itself is paid; output-state notation is used only in proofs. -/
def moved (a : Data) (src dst : Fin 768) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks dst (a.stacks src ++ a.stacks dst)) src []⟩

theorem move_eval (a : Data) (src dst : Fin 768)
    (hsd : src ≠ dst) (hst : src ≠ 159) (htd : (159 : Fin 768) ≠ dst)
    (htmp : a.stacks 159 = []) :
    Eval (move src dst) (9*(a.stacks src).length+8) a (moved a src dst) := by
  have h1 := SubexpScanPrimitives.copy_eval a src dst 159 0 1 hsd hst htd (by decide) htmp
  let b := SubexpScanPrimitives.afterCopy a src dst 0 1
  have h2 : Eval (clear src) (2*(b.stacks src).length+3) b
      ⟨readRegs b.regs 0 1 none,Function.update b.stacks src []⟩ :=
    Eval.call _ (ListRegisterProgram.clear_run src (0 : Fin 40) 1 b.regs b.stacks)
  have hlen : b.stacks src = a.stacks src := by
    simp [b,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,hsd]
  have hout : (⟨readRegs b.regs 0 1 none,Function.update b.stacks src []⟩ : Data) =
      moved a src dst := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [b,SubexpScanPrimitives.afterCopy,StackRoutines.readRegs_reset]
    · rfl
  rw [hout] at h2
  have h := h1.seq h2
  simpa only [move,copy,hlen,show 7*(a.stacks src).length+5+
      (2*(a.stacks src).length+3)=9*(a.stacks src).length+8 by omega] using h


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
