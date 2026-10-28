import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed16/256 frame primitives for beta evaluation. These use the immutable
reader and transfer programs and are independent of the larger moment driver. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaFrames
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 16 256
abbrev Code := Cmd 16 256

abbrev transfer (src dst : Fin 256) : Code := .call (transferProgram src dst 0 1)
abbrev afterTransfer (d : Data) (src dst : Fin 256) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem transfer_eval (d : Data) (src dst : Fin 256) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) d.regs d.stacks)

def framePorts (src dst : Fin 256) (hsd : src ≠ dst) : RecordPrograms.Ports 16 256 where
  tag := 0
  present := 1
  found := 2
  source := src
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := hsd

abbrev readFrame (src dst : Fin 256) (hsd : src ≠ dst) : Code :=
  RecordPrograms.reader (framePorts src dst hsd)

abbrev afterFrame (d : Data) (src dst : Fin 256) (bits tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src tail) dst (bits.reverse ++ d.stacks dst)⟩

theorem readFrame_eval (d : Data) (src dst : Fin 256) (hsd : src ≠ dst)
    (bits tail : List Bool) (hs : d.stacks src = Encoding.frame bits ++ tail) :
    Eval (readFrame src dst hsd) (6*bits.length+4) d (afterFrame d src dst bits tail) := by
  let ports := framePorts src dst hsd
  have h := RecordPrograms.reader_eval ports d bits tail (d.stacks dst)
    (d.regs 0) (d.regs 1) (d.regs 2)
  have hi : RecordPrograms.state ports d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) (d.stacks dst) = d :=
    RecordPrograms.state_eq_self ports d _ _ _ _ _ rfl rfl rfl hs rfl
  rw [hi] at h
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [ ports, framePorts, readRegs]
  · funext i
    simp [ ports, framePorts ]

end SubexponentialSAT.SqrtLog.PerturbationBetaFrames

end OAI.Algorithms
