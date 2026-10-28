import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramMiddle
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramFixed
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram

namespace OAI.Algorithms

/-! One finite instruction table for arbitrary dynamic coefficient degree,
ring precision, node count, and jet order. All such parameters reside on
input tapes. The scalar and polynomial services here are concrete programs. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls

/-- Fixed local correction producer, with native scalar and array services. -/
abbrev localCode : Cmd 16 256 :=
  CRTLocalProgram.localCommand HornerProgram.Services.multiply HornerProgram.Services.add
    DensePolynomialProgram.Fixed.mulCommand DensePolynomialProgram.AddService.command

/-- Fixed arithmetic stage used by every outer-node iteration. -/
abbrev middle : Cmd 16 320 :=
  Middle.command localCode HornerProgram.Services.multiply HornerProgram.Services.add

/-- Cache preparation, physical initialization, node traversal, and cleanup. -/
abbrev command : Cmd 16 320 := .seq Entry.prepare (ReconstructionProgram.controller middle)

abbrev program : Program 16 320 (size command + 1) := compiled command 256 261

/-- The final compilation contributes exactly the ordinary return step. -/
theorem program_run {n : ℕ} {input output : StructuredProgram.State 16 320}
    (h : Eval command n input output) :
    RunsIn program (n + 1) (input.withPC (some program.entry)) (output.withPC none) := by
  exact ⟨n + 1, le_rfl, compiled_halt_trace h 256 261⟩

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
