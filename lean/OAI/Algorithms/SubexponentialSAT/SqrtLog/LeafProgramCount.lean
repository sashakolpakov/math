import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReadbackWide

namespace OAI.Algorithms

/-! One closed native count-recovery table: Hermite reconstruction over the
computed ring, integer readback, and reclamation of the two CRT entry caches.
Node-jet production and its semantic theorem are composed at the caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 40 768
def crtRegisters (i : Fin 16) : Fin 40 := i.castAdd 24
def crtStacks (i : Fin 320) : Fin 768 := i.castAdd 448

abbrev reconstruct : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram ReconstructionProgram.Native.program crtRegisters crtStacks)

abbrev clearCaches : Cmd 40 768 :=
  .seq (.call (StackRoutines.clearProgram 5 0 1)) (.call (StackRoutines.clearProgram 10 0 1))

def cachesCleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update (Function.update a.stacks 5 []) 10 []⟩

theorem clearCaches_eval (a : Data) :
    Eval clearCaches (2*(a.stacks 5).length+2*(a.stacks 10).length+6) a (cachesCleared a) := by
  let b : Data := ⟨readRegs a.regs 0 1 none,Function.update a.stacks 5 []⟩
  have h1 : Eval (.call (StackRoutines.clearProgram 5 0 1)) (2*(a.stacks 5).length+3) a b := by
    exact Eval.call _ (ListRegisterProgram.clear_run (5 : Fin 768) (0 : Fin 40) 1 a.regs a.stacks)
  have h2 : Eval (.call (StackRoutines.clearProgram 10 0 1)) (2*(b.stacks 10).length+3) b
      ⟨readRegs b.regs 0 1 none,Function.update b.stacks 10 []⟩ := by
    exact Eval.call _ (ListRegisterProgram.clear_run (10 : Fin 768) (0 : Fin 40) 1 b.regs b.stacks)
  convert h1.seq h2 using 1 <;>
    simp [cachesCleared,b,StackRoutines.readRegs_reset] ; omega

theorem cachesCleared_frame (a : Data) (i : Fin 768) (h5 : i ≠ 5) (h10 : i ≠ 10) :
    (cachesCleared a).stacks i = a.stacks i := by
  simp [cachesCleared,h5,h10]

@[simp] theorem cachesCleared_five (a : Data) : (cachesCleared a).stacks 5 = [] := by
  simp [cachesCleared]
@[simp] theorem cachesCleared_ten (a : Data) : (cachesCleared a).stacks 10 = [] := by
  simp [cachesCleared]

abbrev command : Cmd 40 768 :=
  .seq reconstruct (.seq QueryReadback.Wide.command clearCaches)

def program := compiled command 256 323

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
