import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-! Fixed native incidence command and its physical port ABI. The definitions
are extracted unchanged from the same emitter-specializer composition. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProgram
open SubexpScanPrimitives SubexpSetupStorage

def lowProgram := compiled PerturbationAssembly.prepareLow 205 217

namespace Native

def lowPorts : Fin 256 → Fin 294 := Fin.castAdd 38

def producerPorts : Fin 38 → Fin 294 := Fin.natAdd 256

def producerRegisters : Fin 8 → Fin 16 := Fin.castAdd 8

theorem lowPorts_injective : Function.Injective lowPorts := Fin.castAdd_injective _ _

theorem producerPorts_injective : Function.Injective producerPorts := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

theorem producerRegisters_injective : Function.Injective producerRegisters :=
  Fin.castAdd_injective _ _

def joinedState (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) : State 16 294 :=
  ⟨regs, fun i => Fin.addCases (m := 256) (n := 38) (motive := fun _ => List Bool) low high i⟩

@[simp] theorem joinedState_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) (i : Fin 256) :
    (joinedState regs low high).stacks (lowPorts i) = low i := by
  simp [joinedState, lowPorts]

@[simp] theorem joinedState_high (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) (i : Fin 38) :
    (joinedState regs low high).stacks (producerPorts i) = high i := by
  simp [joinedState, producerPorts]

def emptyHigh (mask : List Bool) : Fin 38 → List Bool :=
  (state (fun _ => false) [] [] [] [] [] {target := mask}).stacks

def loadPairs : List (Fin 294 × Fin 294) := [(194,261),(202,268),(204,280)]

def loadCommand : Cmd 16 294 :=
  .seq (copyMany 292 loadPairs)
    (.seq (.call (StackRoutines.transferProgram 217 292 0 1))
      (.call (StackRoutines.transferProgram 292 284 0 1)))

def loaded (a : State 16 294) : State 16 294 :=
  afterTransfer (afterTransfer (copyManyState loadPairs a) 217 292 0 1) 292 284 0 1

def outputMove : Cmd 16 294 :=
  .seq (.call (StackRoutines.transferProgram 271 292 0 1))
    (.call (StackRoutines.transferProgram 292 217 0 1))

def movedOutput (a : State 16 294) : State 16 294 :=
  afterTransfer (afterTransfer a 271 292 0 1) 292 217 0 1

def highPorts : List (Fin 294) := (List.finRange 38).map producerPorts

def finishCommand : Cmd 16 294 := .seq outputMove (clearMany highPorts)

def finished (a : State 16 294) : State 16 294 := clearManyState highPorts (movedOutput a)

/-- One fixed native incidence producer over all supplied ambient rows, including immediate specialization,
normalization, result export and complete local high-bank reclamation. -/
def command : Cmd 16 294 :=
  .seq (.call (ProgramLinking.liftProgram lowProgram id lowPorts))
    (.seq loadCommand
      (.seq (.call (ProgramLinking.liftProgram preparedProgram producerRegisters producerPorts))
        finishCommand))

def program := compiled command 205 217

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
