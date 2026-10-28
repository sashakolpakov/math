import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNumerator
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgramPorts

namespace OAI.Algorithms

/-! The fixed source-value table program. Its definitions and structural
interfaces are independent of the full integer numerator execution proof. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open IntegerRingLiftProgram

def numerator : Code := liftCommand LayoutProgram.Numerator.command 23 50
  numeratorRegs numeratorPorts

def callback : Code := .seq numerator (.seq modelScaledCommand
  (.seq (clear 253) (clear 254)))

def tableProgram := LayoutSourceValuesProgram.program callback

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
