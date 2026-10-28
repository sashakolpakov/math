import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpInputBitProgram
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentProducer
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssembly

namespace OAI.Algorithms

/-!
# Raw incidence packets to prepared factor rows

This fixed controller consumes the nested packets produced by the layout
blueprint stage. It computes each residue-field dot product and its lift,
constructs Ce from the physical Taylor cache, and invokes the scalar-literal
row preparer. No Ce value or postfix instruction stream is an input.

The execution refinements are separate from this finite control definition.
-/

namespace SubexponentialSAT.SubexpBlueprintFactor

open BitProgram StructuredCalls

abbrev Word := List Bool
abbrev Data := State 8 128
abbrev Code := Cmd 8 128

/-- All arithmetic and dimension data are runtime words. The point stream
contains source-width constant quartets produced by PointBank. -/
structure Context where
  sourceModulus : Word
  sourceReduction : Word
  sourceWidth : Word
  targetWidth : Word
  sourceZero : Word
  pointStream : Word
  targetModulus : Word
  targetMinusOne : Word
  dimension : ℕ
  indexWidth : ℕ

structure Work where
  input : Word := []
  origin : Word := []
  pointCopy : Word := []
  beta : Word := []
  negative : Word := []
  taylor : Word := []
  coefficients : Word := []
  argument : Word := []
  payload : Word := []
  scratch : Word := []
  parser : Word := []
  coordinate : Word := []
  row : Word := []
  factor : Word := []

/-- Ports below82 are the actual beta machine. Masters90--95 and the
unconsumed raw factor100 lie outside that call's footprint. -/
def state (ctx : Context) (regs : Fin 8 → Bool) (w : Work) : Data :=
  ⟨regs, fun i => match i.val with
    | 66 => ctx.sourceModulus | 73 => ctx.sourceReduction | 74 => ctx.sourceWidth
    | 77 => w.beta | 79 => ctx.targetWidth | 80 => w.origin | 81 => w.pointCopy
    | 90 => ctx.sourceZero | 91 => ctx.pointStream | 92 => ctx.targetModulus
    | 93 => ctx.targetMinusOne | 94 => List.replicate ctx.dimension true
    | 95 => List.replicate ctx.indexWidth true | 100 => w.input
    | 103 => w.negative | 104 => w.taylor | 105 => w.coefficients
    | 106 => w.argument | 107 => w.payload | 108 => w.scratch | 109 => w.parser
    | 110 => w.coordinate | 111 => w.row | 112 => w.factor | _ => []⟩

def serviceState (ctx : Context) (regs : Fin 8 → Bool) (input : Word) : Data :=
  state ctx regs { input := input }

def parserRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def frameRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def preparedRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def parserPorts : Fin 2 → Fin 128 := ![100,109]
def framePorts (src dst : Fin 128) : Fin 3 → Fin 128 := ![src,dst,108]
def betaPorts : Fin 82 → Fin 128 := Fin.castAdd 46

/-- The argument producer shares only the completed beta and required ring
masters with the beta machine. Its remaining work ports are initially empty. -/
def argumentPorts (i : Fin 46) : Fin 128 := match i.val with
  | 4 => 93 | 14 => 92 | 18 => 77 | 19 => 103 | 20 => 79
  | 24 => 104 | 25 => 94 | 26 => 95 | 27 => 106
  | _ => ⟨i.val,by omega⟩

def preparedPorts (i : Fin 22) : Fin 128 := match i.val with
  | 0 => 100 | 1 => 109 | 2 => 110 | 3 => 111 | 4 => 112 | 5 => 113
  | 6 => 114 | 7 => 94 | 8 => 95 | 9 => 115 | 10 => 116 | 11 => 117
  | 12 => 118 | 13 => 119 | 14 => 120 | 15 => 121 | 16 => 122
  | 17 => 123 | 18 => 124 | 19 => 125 | 20 => 126 | _ => 127

def atom (a : StructuredProgram.Atom 8 128) : Code := .base (.atom a)
local infixr:60 " ;; " => Cmd.seq

def transfer (src dst : Fin 128) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)
def clear (src : Fin 128) : Code := .call (StackRoutines.clearProgram src (0 : Fin 8) 1)
def copy (src dst : Fin 128) : Code :=
  .call (StackRoutines.copyProgram src dst 108 (0 : Fin 8) 1)
def pushBit (dst : Fin 128) (b : Bool) : Code := atom (.set 0 b) ;; atom (.push dst 0)

def popTag : Code := atom (.pop 100 0 1)
def unframe : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.unframeProgram parserRegs parserPorts)

/-- The parser writes reversed bits to109; the transfer restores their
forward order at the named destination. -/
def capture (dst : Fin 128) : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram parserRegs parserPorts) ;;
    transfer 109 dst

def appendFrame (src dst : Fin 128) : Code :=
  atom (.set 2 true) ;;
    .call (ProgramLinking.liftProgram SubexpBlockAssembly.frameBody frameRegs (framePorts src dst))

def appendRecord (src dst : Fin 128) : Code := pushBit dst true ;; appendFrame src dst

def packComplete (src dst : Fin 128) : Code :=
  transfer src 107 ;; appendRecord 107 dst ;; clear 107

def closeList (src dst : Fin 128) : Code := pushBit src false ;; packComplete src dst

def scan (body : Code) : Code := popTag ;; .while 0 (unframe ;; body ;; popTag)

def computeBeta : Code := copy 90 77 ;; copy 91 81 ;;
  .call (ProgramLinking.liftProgram SubexpInputBitProgram.sourceProgram id betaPorts)

def computeArgument : Code := pushBit 106 false ;;
  .call (ProgramLinking.liftProgram SubexpArgumentProducer.program id argumentPorts)

/-- The first unframe exposes the origin/Taylor pair nested inside the
coordinate packet. The selected scalar coefficient list is copied as data;
the final row preparer constructs each of its raw scalar literals. -/
def coordinateBody : Code :=
  unframe ;; capture 80 ;; capture 104 ;; capture 105 ;;
  computeBeta ;; computeArgument ;;
  appendFrame 106 110 ;; transfer 105 110 ;;
  clear 106 ;; clear 103 ;; clear 77 ;; clear 104 ;; packComplete 110 111

def rowBody : Code :=
  capture 107 ;; appendFrame 107 111 ;; clear 107 ;;
    scan coordinateBody ;; closeList 111 112

def reset : Code := atom (.set 0 false) ;; atom (.set 1 false) ;;
  atom (.set 2 false) ;; atom (.set 3 false) ;; atom (.set 4 false) ;;
  atom (.set 5 false) ;; atom (.set 6 false) ;; atom (.set 7 false)

def rawRows : Code := scan rowBody ;; pushBit 112 false ;; transfer 112 100

/-- The final call is agent47's actual scalar-literal row traversal, not a
map performed by the mathematical host. -/
def command : Code := rawRows ;; reset ;;
  .call (ProgramLinking.liftProgram SubexpPreparedFactor.program preparedRegs preparedPorts)

def program := StructuredCalls.compiled command 100 100

end SubexponentialSAT.SubexpBlueprintFactor

end OAI.Algorithms
