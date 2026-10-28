import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRowStream
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-!
# Fixed outer factor-packet control

The two master streams are traversed together. Each prefix-group record carries
its physically counted unary arity and its incidence-prefix stream. The Boolean
table record is consumed in reverse rank order by the row serializer, which
restores its original order. A final record reversal restores factor order.

Masters40..45: complete Lagrange cache, prefix groups, Boolean tables, binary
modulus, target zero, target one. Output47 is the only master-level change.
-/

namespace SubexponentialSAT.SubexpFactorPacketControl

open BitProgram StructuredCalls

abbrev Word := List Bool
abbrev Data := State 8 64
abbrev Command := Cmd 8 64

def rowPorts : Fin 26 → Fin 64 :=
  ![0,1,2,3,4,43,6,7,8,9,10,11,12,13,51,15,16,53,44,45,20,21,54,23,24,25]
def factorPorts : Fin 22 → Fin 64 :=
  ![0,1,2,3,4,5,6,40,8,9,10,11,55,54,14,15,16,17,18,19,56,21]
def writerRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def writerPorts : Fin 6 → Fin 64 := ![0,50,1,46,2,3]
def reverseRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def reversePorts : Fin 4 → Fin 64 := ![46,58,47,59]

theorem rowPorts_injective : Function.Injective rowPorts := by decide
theorem factorPorts_injective : Function.Injective factorPorts := by decide
theorem writerRegs_injective : Function.Injective writerRegs := Fin.castAdd_injective _ _
theorem writerPorts_injective : Function.Injective writerPorts := by decide
theorem reverseRegs_injective : Function.Injective reverseRegs := Fin.castAdd_injective _ _
theorem reversePorts_injective : Function.Injective reversePorts := by decide

def copy (src dst : Fin 64) : Command :=
  .call (StackRoutines.copyProgram src dst 60 (0 : Fin 8) 1)
def transfer (src dst : Fin 64) : Command :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)
def clear (src : Fin 64) : Command :=
  .call (StackRoutines.clearProgram src (0 : Fin 8) 1)
def seed (dst : Fin 64) : Command :=
  Subexp.TupleProgram.pushConst dst (0 : Fin 8) false

def rows : Command := .call
  (ProgramLinking.liftProgram SubexpFactorRowStream.program id rowPorts)
def factor : Command := .call
  (ProgramLinking.liftProgram Subexp.FactorPacketRows.program id factorPorts)
def emitFactor : Command := .call
  (ProgramLinking.liftProgram (SubexpArgumentProgram.writer true) writerRegs writerPorts)
def reverseFactors : Command := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram reverseRegs reversePorts)

def readTags : Command :=
  .seq (SubexpInputFrames.readTag 48) (.base (.atom (.pop 49 0 1)))

def readGroup : Command :=
  .seq (SubexpInputFrames.readField 48 50 (by decide))
    (.seq (transfer 50 57)
      (.seq (SubexpInputFrames.readField 57 51 (by decide))
        (.seq (SubexpInputFrames.readField 57 52 (by decide)) (transfer 52 55))))

def readTable : Command := SubexpInputFrames.readField 49 53 (by decide)

def makeFactor : Command := .seq readGroup (.seq readTable (.seq rows (.seq factor
  (.seq (transfer 56 50) (.seq emitFactor (.seq (clear 51) (clear 55)))))))

def loop : Command := .while 7 (.seq makeFactor readTags)
def prepare : Command := .seq (copy 41 48) (.seq (copy 42 49)
  (.seq (seed 46) (seed 47)))
def command : Command := .seq prepare (.seq readTags (.seq loop reverseFactors))
def program := compiled command (42 : Fin 64) 47

structure Masters where
  cache : Word
  groups : Word
  tables : Word
  modulus : Word
  zero : Word
  one : Word

def store (m : Masters) : Fin 64 → Word := fun i =>
  if i = 40 then m.cache else if i = 41 then m.groups else if i = 42 then m.tables
  else if i = 43 then m.modulus else if i = 44 then m.zero else if i = 45 then m.one else []

def state (regs : Fin 8 → Bool) (m : Masters) : Data := ⟨regs, store m⟩

def outputState (regs : Fin 8 → Bool) (m : Masters) (output : Word) : Data :=
  ⟨regs, Function.update (store m) 47 output⟩

end SubexponentialSAT.SubexpFactorPacketControl

end OAI.Algorithms
