import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheEncoding
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeScalarCalls
import OAI.Algorithms.SubexponentialSAT.SubexpLocalLinearFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialMultiplyService
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialIterationControl
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPowerProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryCompare
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCachePreparation

namespace OAI.Algorithms

/-!
# Fixed control for the complete target Lagrange cache

The eight preserved inputs are prime206, unit207, modulus208, width209,
reduction210, minusOne211, precision224, and Fermat exponent225. Output250
holds the complete framed cache. All other stacks start and end empty.

The inverse slot below is a fixed command supplied by the flat inverse
adapter. It is not a semantic callback or a function-to-program compiler.
The final cache module instantiates it with that adapter's actual program.
-/

namespace SubexponentialSAT.SubexpLagrangeCacheControl

open BitProgram StructuredCalls SubexpConvolutionControl

abbrev Data := State 16 256
abbrev Code := Cmd 16 256
abbrev Word := List Bool

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def lowRegisters : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective _ _⟩
def threeRegisters : Fin 3 ↪ Fin 16 := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
def fiveRegisters : Fin 5 ↪ Fin 16 := ⟨Fin.castAdd 11, Fin.castAdd_injective _ _⟩

def conversionPorts : Fin 3 ↪ Fin 256 := ⟨![0, 243, 1], by decide⟩
def allocationPorts : Fin 4 ↪ Fin 256 := ⟨![104, 242, 228, 227], by decide⟩
def initializePorts : Fin 128 ↪ Fin 256 := ⟨Fin.castAdd 128, Fin.castAdd_injective _ _⟩

def convertPrime : Code :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram
    threeRegisters conversionPorts)

def initializeZero : Code :=
  .call (ProgramLinking.liftProgram
    (compiled SubexpLinearFactorProgram.initializeCell 10 104) id initializePorts)

def allocate : Code :=
  .call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
    threeRegisters allocationPorts)

def compareRegisters : Fin 10 ↪ Fin 16 := ⟨Fin.castAdd 6, Fin.castAdd_injective _ _⟩

def comparePorts (i : Fin 46) : Fin 256 :=
  if i = 23 then 248 else if i = 24 then 249 else if i = 42 then 120 else
  if i = 43 then 236 else if i = 44 then 237 else if i = 45 then 238 else i.castAdd 210

theorem comparePorts_injective : Function.Injective comparePorts := by decide

def compareIndices : Code :=
  .call (ProgramLinking.liftProgram Subexp.ConstraintEntryCompare.program
    compareRegisters comparePorts)

def scalarAdd : Code := SubexpLocalLinearFactorProgram.scalarAdd
def scalarMultiply : Code :=
  .call (ProgramLinking.liftProgram SubexpQuarticFlatMul.program
    SubexpConvolutionPair.regPort SubexpConvolutionPair.highPort)

def move (src dst : Fin 256) : Code := SubexpPolynomialConstructor.move src dst

def multiplyPolynomial : Code :=
  SubexpPolynomialMultiplyService.command ;; SubexpPolynomialIterationControl.commit

/-- Increment a target-ring integer word by the preserved target one. -/
def increment (dst : Fin 256) : Code :=
  SubexpLagrangeScalarCalls.addTo dst 207 dst

/-- Multiply the scalar denominator by i-j and the polynomial by X-j.
The linear-factor routine also leaves the actual negative-j word on219. -/
def innerProduct : Code :=
  SubexpLocalLinearFactorProgram.command ;;
    SubexpLagrangeScalarCalls.addTo 217 219 214 ;;
    SubexpLagrangeScalarCalls.multiplyTo 205 214 205 ;; clear 214 ;;
    multiplyPolynomial ;; clear 241 ;; clear 219

def innerStep : Code :=
  compareIndices ;; .ite 7 (.base .skip) innerProduct ;;
    increment 218 ;; appendIndex 249

def innerCounter : UnaryForPrograms.Ports 16 256 := ⟨247, 0, 1⟩
def innerLoop : Code := UnaryForPrograms.forCmd innerCounter innerStep

def powerPorts (i : Fin 83) : Fin 256 :=
  if i = 78 then 225 else if i = 80 then 215 else if i = 81 then 216
  else if i = 82 then 219 else ⟨128 + i.val, by omega⟩

theorem powerPorts_injective : Function.Injective powerPorts := by decide

def seed : Code :=
  .call (ProgramLinking.liftProgram SubexpQuarticPowerProgram.program
    lowRegisters powerPorts)

/-- The bank adapter may reuse the low arithmetic workspace, excluding
the live modulus5 and width10. Its nine retained inputs are wired explicitly. -/
def inversePorts (i : Fin 96) : Fin 256 :=
  if i = 5 then 96 else if i = 10 then 97 else
  if i = 76 then 194 else if i = 82 then 205 else if i = 83 then 215 else
  if i = 84 then 201 else if i = 85 then 207 else if i = 86 then 211 else
  if i = 87 then 202 else if i = 88 then 224 else if i = 89 then 214 else
  i.castAdd 160

theorem inversePorts_injective : Function.Injective inversePorts := by decide

def rowPorts : Fin 11 ↪ Fin 256 :=
  ⟨![240, 104, 226, 229, 230, 231, 232, 233, 234, 250, 235], by decide⟩

def writeRow : Code := copy 243 229 ;;
  .call (ProgramLinking.liftProgram SubexpLagrangeCacheEncoding.program
    fiveRegisters rowPorts)

def normalize (inverse : Code) : Code :=
  inverse ;; clear 205 ;;
    copy 214 100 ;; copy 104 101 ;;
    SubexpPolynomialConstructor.constructAtInputs 241 ;;
    clear 214 ;; multiplyPolynomial ;; clear 241

def initializeRow : Code :=
  copy 207 205 ;;
    SubexpPolynomialConstructor.construct 207 104 240 ;;
    copy 213 218 ;; copy 243 247

def outerStep (inverse : Code) : Code :=
  initializeRow ;; innerLoop ;;
    clear 218 ;; clear 249 ;; normalize inverse ;; writeRow ;;
    increment 217 ;; appendIndex 248

def outerCounter : UnaryForPrograms.Ports 16 256 := ⟨246, 0, 1⟩
def outerLoop (inverse : Code) : Code := UnaryForPrograms.forCmd outerCounter (outerStep inverse)

def reversePorts : Fin 4 ↪ Fin 256 := ⟨![250, 236, 237, 238], by decide⟩
def reverseCache : Code :=
  Subexp.TupleProgram.pushConst 237 0 false ;;
    .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
      threeRegisters reversePorts) ;; move 237 250

def prepare : Code :=
  SubexpLagrangeCachePreparation.command

def cleanup : Code :=
  clear 217 ;; clear 248 ;; clear 5 ;; clear 10 ;; clear 104 ;;
    clear 194 ;; clear 201 ;; clear 202 ;; clear 213 ;; clear 242 ;; clear 243

def command (inverse : Code) : Code :=
  prepare ;; outerLoop inverse ;; reverseCache ;; cleanup

end SubexponentialSAT.SubexpLagrangeCacheControl

end OAI.Algorithms
