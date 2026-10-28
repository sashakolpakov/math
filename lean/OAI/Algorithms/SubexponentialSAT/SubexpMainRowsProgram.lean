import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowCode

namespace OAI.Algorithms

/-! The fixed Main row-table program, separated from its semantic proof. -/

namespace SubexponentialSAT.SubexpMainRows

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary)

def row (er : ℕ) (hr : 16 ≤ er) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 25
  stackCount := 288
  labels := size SubexpDenseRowCode.command + 1
  program := SubexpDenseRowCode.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨fun i => ordinary alloc ⟨i.val, by omega⟩, by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (totalStacks es) => q.val) h)⟩

def procedure (er : ℕ) (hr : 16 ≤ er) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainRowPreparation.procedure er alloc) (row er hr alloc)

def program (er : ℕ) (hr : 16 ≤ er) {es : ℕ} (alloc : Allocation es) :=
  (procedure er hr alloc).program

end SubexponentialSAT.SubexpMainRows

end OAI.Algorithms
