import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorDispatch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorID
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidence
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramExpansionForward
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIndicator
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramClause
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram

namespace OAI.Algorithms

/-! Fixed per-assignment factor evaluation. Factors are dispatched by runtime
ID; hash rows are expanded and tested by the computed idempotent, the marked
clause is multiplied directly, and added neutral factors contribute one.
Every operation below is an actual finite instruction table or native loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

/-- The indicator's coefficient port78 is relocated; runtime theta78 stays
available to every subsequent source-row computation. -/
def indicatorStacks (i : Fin 96) : Fin 768 :=
  Equiv.swap 78 143 (nativeStacks i)

def indicatorReady : Code := .seq (.base (.atom (.set 0 false)))
  (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 2 false))))
def indicator : Code := .seq indicatorReady
  (.call (ProgramLinking.liftProgram Indicator.program nativeRegisters indicatorStacks))
def prepareIncidence : Code := .seq FactorID.command Incidence.caller

def hashFactor : Code := .seq prepareIncidence
  (.seq Expansion.forwardCommand
    (.seq indicator (.seq (clear 68) (.seq (clear 62) accumulate))))

def markedFactor : Code := .seq prepareIncidence
  (.seq (move 154 63) (.seq Clause.caller (.seq (clear 62) accumulate)))

/-- The role flag is tested before any arithmetic or source worker can reuse
its registers. The neutral case performs no source lookup. -/
def choose : Code := .ite 5 hashFactor (.ite 6 markedFactor (.base .skip))

def returnToRecords : Code := .seq (.base (.atom (.set 13 false)))
  (.seq (.base (.atom (.set 14 true))) (.base (.atom (.set 15 false))))
def ports : RecordPrograms.Ports 40 768 :=
  ⟨13,14,15,150,149,by decide,by decide,by decide,by decide⟩
def callback : Code := .seq FactorDispatch.command
  (.seq choose (.seq (clear 149) returnToRecords))
def loop : Code := RecordPrograms.iterate ports callback

def command : Code := .seq (copy 175 150)
  (.seq (copy 69 151) (.seq loop (move 151 67)))
def program := compiled command 175 67

/-- Complete assignment callback expected by the wide moment assembler. The
before/after helpers save the current head sums/products, form the actual
bucket/head choice, compute its Boolean weight, and restore the caller. -/
def assignment : Code := .seq LeafAssignmentSetupProgram.beforeCommand
  (.seq command LeafAssignmentSetupProgram.afterCommand)
def assignmentProgram := compiled assignment 174 41

theorem indicatorStacks_injective : Function.Injective indicatorStacks :=
  (Equiv.swap 78 143).injective.comp nativeStacks_injective

@[simp] theorem coefficient_port : indicatorStacks 78 = 143 := by decide
@[simp] theorem factor_result_port : indicatorStacks 67 = 67 := by decide

theorem indicator_theta_frame (frame : Data) (b : State 8 96) :
    (embedState nativeRegisters indicatorStacks frame b).stacks 78 = frame.stacks 78 :=
  embedState_stack_frame nativeRegisters indicatorStacks frame b 78 (by
    rintro ⟨j, hj⟩
    change Equiv.swap 78 143 (nativeStacks j) = 78 at hj
    rw [Equiv.swap_apply_eq_iff] at hj
    have hv := congrArg Fin.val hj
    simp [nativeStacks] at hv
    omega)

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end
end OAI.Algorithms
