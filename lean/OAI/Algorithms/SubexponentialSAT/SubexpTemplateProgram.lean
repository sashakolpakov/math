import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPointBank
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorBlueprint

namespace OAI.Algorithms

/-!
# One-time preparation of an unweighted moment template

The input contains actual base/increment banks, support records, and raw
factor packets. Every inner point is added in Fp by the PointBank program;
each factor then computes beta, Ce, and its prepared literal rows. The output
is the unweighted template reused by the current-exponent source constructor.

Only finite control and its exact byte schema are defined here. Execution
and budget refinements must establish the calls and packing, not assume the
whole output template.
-/

namespace SubexponentialSAT.SubexpTemplateProgram

open BitProgram StructuredCalls

abbrev Word := List Bool
abbrev Data := State 8 142
abbrev Code := Cmd 8 142

structure Term where
  increment : Word
  support : Word
  factors : List (List Subexp.FactorBlueprint.Row)

structure Block where
  base : Word
  outsideSupport : Word
  groups : List (List Term)

def encodeTerm (t : Term) : Word :=
  Encoding.frame t.increment ++ Encoding.frame t.support ++
    Encoding.frame (Encoding.encodeList Subexp.FactorBlueprint.encodeRows t.factors)

def encodeGroup (ts : List Term) : Word := Encoding.encodeList encodeTerm ts

def encodeBlock (b : Block) : Word :=
  Encoding.frame b.base ++ Encoding.frame b.outsideSupport ++
    Encoding.encodeList encodeGroup b.groups

def encodeBlocks (bs : List Block) : Word := Encoding.encodeList encodeBlock bs

def parserRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def frameRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def parserPorts : Fin 2 → Fin 142 := ![130,136]
def framePorts (src dst : Fin 142) : Fin 3 → Fin 142 := ![src,dst,141]
def factorPorts : Fin 128 → Fin 142 := Fin.castAdd 14

/-- The point program shares source modulus/width/dimension masters with the
factor program; its scalar and quartet outputs feed the descriptor and beta
input respectively. Addition occurs before the target-width weight lift. -/
def pointPorts (i : Fin 32) : Fin 142 := match i.val with
  | 5 => 66 | 10 => 74 | 20 => 138 | 21 => 91
  | 22 => 128 | 23 => 137 | 24 => 94 | _ => ⟨i.val,by omega⟩

def atom (a : StructuredProgram.Atom 8 142) : Code := .base (.atom a)
local infixr:60 " ;; " => Cmd.seq

def transfer (src dst : Fin 142) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)
def clear (src : Fin 142) : Code := .call (StackRoutines.clearProgram src (0 : Fin 8) 1)
def pushBit (dst : Fin 142) (b : Bool) : Code := atom (.set 0 b) ;; atom (.push dst 0)

def popTag : Code := atom (.pop 130 0 1)
def unframe : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.unframeProgram parserRegs parserPorts)
def capture (dst : Fin 142) : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram parserRegs parserPorts) ;;
    transfer 136 dst

def appendFrame (src dst : Fin 142) : Code := atom (.set 2 true) ;;
  .call (ProgramLinking.liftProgram SubexpBlockAssembly.frameBody frameRegs (framePorts src dst))
def appendRecord (src dst : Fin 142) : Code := pushBit dst true ;; appendFrame src dst

def packComplete (src dst : Fin 142) : Code :=
  transfer src 135 ;; appendRecord 135 dst ;; clear 135
def closeList (src dst : Fin 142) : Code := pushBit src false ;; packComplete src dst

def scanBare (body : Code) : Code := popTag ;; .while 0 (body ;; popTag)
def scan (body : Code) : Code := scanBare (unframe ;; body)

/-- Capture a whole factor on its private input port. The called program
reads actual origin/Taylor/cache packets and constructs prepared rows. -/
def factorBody : Code := capture 100 ;;
  .call (ProgramLinking.liftProgram SubexpBlueprintFactor.program id factorPorts) ;;
  appendRecord 100 134 ;; clear 100

/-- The factor list is a framed field in the target term. Its terminator is
inserted once, before that enclosing frame is emitted. -/
def finishFactors : Code := pushBit 134 false ;; transfer 134 135 ;;
  appendFrame 135 133 ;; clear 135

def termBody : Code :=
  capture 137 ;; capture 129 ;; unframe ;;
  .call (ProgramLinking.liftProgram SubexpPointBank.program id pointPorts) ;;
  appendFrame 138 133 ;; clear 138 ;;
  appendFrame 129 133 ;; clear 129 ;;
  scanBare factorBody ;; finishFactors ;;
  clear 91 ;; clear 137 ;; packComplete 133 132

def groupBody : Code := scan termBody ;; closeList 132 131

/-- The outside point is the already canonical base. Only inner terms need
base-plus-increment addition and a quartet stream for their factors. -/
def blockBody : Code := capture 128 ;; capture 129 ;;
  appendFrame 128 131 ;; appendFrame 129 131 ;; clear 129 ;;
  scan groupBody ;; clear 128 ;; closeList 131 140

def command : Code := scan blockBody ;; pushBit 140 false ;; transfer 140 139
def program := StructuredCalls.compiled command 130 139

end SubexponentialSAT.SubexpTemplateProgram

end OAI.Algorithms
