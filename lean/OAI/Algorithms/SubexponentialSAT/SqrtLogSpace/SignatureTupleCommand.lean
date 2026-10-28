import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoadCommand
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram

/-! The fixed actual attained-signature tuple command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
noncomputable section

/-- The concrete DFS table has no algorithm-service arguments. -/
def routines : Routines 40 896 :=
  assembleRoutines SignatureTupleLoader.loadHead candidateCall QueryVisitorProgram.visitor

abbrev command : Cmd 40 896 := SignatureTupleProgram.command controllerPorts routines

def program := compiled command 837 851

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
