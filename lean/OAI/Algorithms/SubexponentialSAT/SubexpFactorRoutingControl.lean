import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHeadColorProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Fixed control for routing original factors by their assignment color

Masters 0/1 are the flat assignment and original factor records. Master 2
contains the requested color as a little-endian word, and master 3 is the
unary node index. Master 4 is unary color width; only the length of the
assignment-word-width buffer 5 matters. Only output 6
changes at the public boundary. Each iteration consumes one assignment
word and one factor record, so duplicate factor payloads remain distinct.
-/

namespace SubexponentialSAT.SubexpFactorRoutingControl

open BitProgram StructuredCalls

abbrev Data := State 16 48
abbrev Command := Cmd 16 48

def registers3 : Fin 3 → Fin 16 := Fin.castAdd 13
def registers5 : Fin 5 → Fin 16 := Fin.castAdd 11

theorem registers3_injective : Function.Injective registers3 := Fin.castAdd_injective _ _
theorem registers5_injective : Function.Injective registers5 := Fin.castAdd_injective _ _

def colorPorts : Fin 10 → Fin 48 := ![10,13,4,11,14,15,16,17,18,19]
def conversionPorts (dst : Fin 48) : Fin 3 → Fin 48 := ![24,dst,25]
def equalityPorts : Fin 2 → Fin 48 := ![11,22]
def reversePorts : Fin 4 → Fin 48 := ![23,27,6,28]

theorem colorPorts_injective : Function.Injective colorPorts := by decide
theorem equalityPorts_injective : Function.Injective equalityPorts := by decide
theorem reversePorts_injective : Function.Injective reversePorts := by decide
theorem conversionPorts_injective (dst : Fin 48) (h24 : dst ≠ 24) (h25 : dst ≠ 25) :
    Function.Injective (conversionPorts dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [conversionPorts]

def parserPorts : RecordPrograms.Ports 16 48 :=
  ⟨13,14,15,8,9,by decide,by decide,by decide,by decide⟩

def emitPorts : RecordPrograms.Ports 16 48 :=
  ⟨0,1,2,9,23,by decide,by decide,by decide,by decide⟩

def copy (src dst : Fin 48) : Command :=
  .call (StackRoutines.copyProgram src dst 26 (0 : Fin 16) 1)

def transfer (src dst : Fin 48) : Command :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 16) 1)

def clear (src : Fin 48) : Command :=
  .call (StackRoutines.clearProgram src (0 : Fin 16) 1)

def convertIndex (dst : Fin 48) : Command :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram
    registers3 (conversionPorts dst))

def readColor : Command :=
  .call (ProgramLinking.liftProgram SubexpHeadColorProgram.program registers5 colorPorts)

def compareColors : Command :=
  .call (ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram registers5 equalityPorts)

def takeWord : Command :=
  .call (ArrayPrograms.countedTransferProgram (20 : Fin 48) 7 21 (0 : Fin 16) 1)

def pullWord : Command := .seq (copy 5 20) (.seq takeWord (transfer 21 10))

def emit : Command :=
  .seq (Subexp.TupleProgram.pushConst 23 0 false)
    (.seq (Subexp.TupleProgram.escape emitPorts) (Subexp.TupleProgram.pushConst 23 0 true))

def callback : Command :=
  .seq pullWord (.seq readColor (.seq (clear 10) (.seq (copy 12 22)
    (.seq compareColors (.seq (clear 11) (.seq (clear 22) (.ite 4 emit (clear 9))))))))

def prepareIndices : Command :=
  .seq (copy 2 24) (.seq (convertIndex 12) (copy 3 13))

def prepare : Command :=
  .seq (copy 0 7) (.seq (copy 1 8) (.seq prepareIndices
    (.seq (Subexp.TupleProgram.pushConst 23 0 false) (Subexp.TupleProgram.pushConst 6 0 false))))

def reverseRecords : Command :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    registers3 reversePorts)

def finish : Command :=
  .seq reverseRecords (.seq (clear 7) (.seq (clear 12) (.seq (clear 13) RegisterResetProgram.all)))

def command : Command := .seq prepare (.seq (RecordPrograms.iterate parserPorts callback) finish)
abbrev program : Program 16 48 (size command + 1) := compiled command 0 6

/-- Scratch is empty at the public boundary; all six masters may contain data. -/
def Clean (d : Data) : Prop := ∀ i : Fin 48, 6 ≤ i.val → d.stacks i = []

def result (d : Data) (bits : List Bool) : Data :=
  ⟨fun _ => false, Function.update d.stacks 6 bits⟩

def readColorBudget (t r : ℕ) : ℕ := SubexpHeadColorProgram.budget t r + 1

/-- Includes word extraction, color reading, comparison, cleanup, and emission. -/
def callbackBudget (W t r g L : ℕ) : ℕ :=
  16 * W + readColorBudget t r + 9 * g + 11 * r + 5 * L + 100

end SubexponentialSAT.SubexpFactorRoutingControl

end OAI.Algorithms
