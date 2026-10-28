import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasisPorts
import OAI.Algorithms.SubexponentialSAT.SubexpLocalBasisControl

namespace OAI.Algorithms

/-! Fixed Main instruction table for the local-basis batch, independent of
the mathematical correctness theorem for the returned basis records. -/

namespace SubexponentialSAT.SubexpMainLocalBasis

open BitProgram StructuredCalls SubexpMainProgram SubexpLayoutPorts

def procedure (er : ℕ) (hr : 16 ≤ er) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 32
  stackCount := 131
  labels := size SubexpLocalBasisControl.command + 1
  program := SubexpLocalBasisControl.program
  register := SubexpMainLocalBasisPorts.registers er hr
  stack := ⟨SubexpMainLocalBasisPorts.stackMap alloc,
    SubexpMainLocalBasisPorts.stackMap_injective alloc⟩

def program (er : ℕ) (hr : 16 ≤ er) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er hr alloc).program
    (procedure er hr alloc).registerMap (procedure er hr alloc).stack

end SubexponentialSAT.SubexpMainLocalBasis

end OAI.Algorithms
