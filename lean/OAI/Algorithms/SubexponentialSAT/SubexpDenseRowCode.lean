import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowLookup
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpRowToTaylorCalls

namespace OAI.Algorithms

/-! The fixed dense-row table program, exposed independently of its
correctness proof. All loop dimensions and arithmetic words are runtime
inputs. This is the same code used by `SubexpDenseRowProducer`. -/

namespace SubexponentialSAT.SubexpDenseRowCode

open BitProgram StructuredCalls SubexpDenseRowTableProgram

def rowCommand : Code :=
  SubexpGlobalRowLookup.row Subexp.UniversalRowAssembly.callerCommand
    SubexpRowToTaylorCalls.command

def command : Code := SubexpDenseRowTableProgram.command rowCommand

def program := SubexpDenseRowTableProgram.program rowCommand

end SubexponentialSAT.SubexpDenseRowCode

end OAI.Algorithms
