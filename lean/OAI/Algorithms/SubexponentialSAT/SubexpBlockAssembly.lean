import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpKernelControl
import OAI.Algorithms.SubexponentialSAT.SubexpTableSource
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Concrete assembly of prepared factors into weighted blocks

Prepared input contains raw weight literals and table rows, never factor
instruction streams. A fixed table-source service is called once per factor.
All surrounding product construction and nested record packing is fixed
Boolean/stack control. The service's local trace contract is instantiated by
the separate prepared-table source proof.
-/

namespace SubexponentialSAT.SubexpBlockAssembly

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

structure Term where
  weight : Word
  factors : List (List SubexpTableSource.Row)

structure Block where
  outside : Word
  groups : List (List Term)

def encodeTerm (t : Term) : Word :=
  Encoding.frame t.weight ++ Encoding.encodeList SubexpTableSource.encodeRows t.factors

def encodeGroup (ts : List Term) : Word := Encoding.encodeList encodeTerm ts

def encodeBlock (b : Block) : Word :=
  Encoding.frame b.outside ++ Encoding.encodeList encodeGroup b.groups

def encodeBlocks (bs : List Block) : Word := Encoding.encodeList encodeBlock bs

def factorProduct (zero one : Word) (fs : List (List SubexpTableSource.Row)) : Word :=
  (fs.map (SubexpTableSource.tableCode zero one)).flatten ++
    SubexpKernelControl.pushWord one ++ SubexpKernelControl.operators true fs.length

def compiledTerm (zero one : Word) (t : Term) : SubexpKernelControl.Term :=
  ⟨t.weight, factorProduct zero one t.factors⟩

def compiledBlock (zero one : Word) (b : Block) : SubexpKernelControl.Block :=
  ⟨b.outside, b.groups.map (fun ts => ts.map (compiledTerm zero one))⟩

def assembled (zero one : Word) (bs : List Block) : Word :=
  SubexpKernelControl.encodeBlocks (bs.map (compiledBlock zero one))

/-! The existing literal program has a public entry immediately before its
framing loop. Reusing this entry omits only the push-opcode prefix. -/

abbrev frameBody : Program 3 3 13 :=
  { SubexpHornerProgram.Literal.program with entry := 3 }

theorem frameBody_trace (payload output : Word) (v p : Bool) :
    Trace frameBody (8 * payload.length + 6)
      (SubexpHornerProgram.Literal.cfg (some 3) v p true payload output [])
      (SubexpHornerProgram.Literal.cfg none false false true payload
        ((Encoding.frame payload).reverse ++ output) []) := by
  have hc := SubexpHornerProgram.Literal.copy_trace payload output [] v p
  have hr := SubexpHornerProgram.Literal.restore_trace payload.reverse []
    ((Encoding.frame payload).reverse ++ output) false false
  simp only [List.append_nil] at hc
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  convert hc.trans hr using 1
  all_goals omega

abbrev Data := State 3 22
abbrev Code := Cmd 3 22

private def atom (a : StructuredProgram.Atom 3 22) : Code := .base (.atom a)
local infixr:60 " ;; " => Cmd.seq

def pairPorts (a b : Fin 22) : Fin 2 → Fin 22 := ![a,b]
def triplePorts (a b c : Fin 22) : Fin 3 → Fin 22 := ![a,b,c]
def parserRegs : Fin 2 → Fin 3 := Fin.castAdd 1

/-- Stream0; constants1/2; table workspace3,5–12; parser4;
product13/count14; term15; group16; block17; blocks18; payload19;
framer20; block's group list21. -/
def tablePorts : Fin 11 → Fin 22 := ![19,1,2,3,5,6,7,8,9,10,11]

def transfer (src dst : Fin 22) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 3) 1)

def clear (src : Fin 22) : Code := .call (StackRoutines.clearProgram src (0 : Fin 3) 1)

def popTag : Code := atom (.pop 0 0 1)

def unframe : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.unframeProgram parserRegs (pairPorts 0 4))

/-- Capture one frame as a forward raw payload on19. -/
def capture : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram parserRegs (pairPorts 0 4)) ;;
    transfer 4 19

def pushBit (dst : Fin 22) (bit : Bool) : Code := atom (.set 0 bit) ;; atom (.push dst 0)

/-- Preserve a raw payload while appending its frame to a reversed output. -/
def appendFrame (src dst : Fin 22) : Code :=
  atom (.set 2 true) ;;
    .call (ProgramLinking.liftProgram frameBody id (triplePorts src dst 20))

def appendRecord (src dst : Fin 22) : Code := pushBit dst true ;; appendFrame src dst

def appendLiteral (src dst : Fin 22) : Code :=
  .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program id
    (triplePorts src dst 20))

def appendCapturedRecord (dst : Fin 22) : Code := capture ;; appendRecord 19 dst ;; clear 19

def productPorts : Fin 8 → Fin 22 := ![0,1,2,13,20,14,12,3]

def drainProducts : Code :=
  .call (ProgramLinking.liftProgram
    (StructuredCalls.compiled (SubexpKernelControl.drain 5 true) 0 3) id productPorts)

/-- Finish a reversed list/object, frame it into its parent, and clean the
temporary forward payload. -/
def closeInto (src dst : Fin 22) : Code :=
  pushBit src false ;; transfer src 19 ;; appendRecord 19 dst ;; clear 19

def scan (body : Code) : Code := popTag ;; .while 0 (unframe ;; body ;; popTag)

def reset : Code := atom (.set 0 false) ;; atom (.set 1 false) ;; atom (.set 2 false)

/-- Table records are extracted into a separate port because their source
service consumes its complete input rather than a prefix of the outer stream. -/
abbrev factorBody {l : ℕ} (table : Program 3 11 l) : Code :=
  capture ;; reset ;; .call (ProgramLinking.liftProgram table id tablePorts) ;;
    transfer 19 13 ;; pushBit 14 true

abbrev scanFactors {l : ℕ} (table : Program 3 11 l) : Code :=
  popTag ;; .while 0 (factorBody table ;; popTag)

abbrev productCommand {l : ℕ} (table : Program 3 11 l) : Code :=
  scanFactors table ;; appendLiteral 2 13 ;; drainProducts ;; transfer 13 19

abbrev termBody {l : ℕ} (table : Program 3 11 l) : Code :=
  appendCapturedRecord 15 ;; productCommand table ;;
    appendRecord 19 15 ;; clear 19 ;; closeInto 15 16

abbrev groupBody {l : ℕ} (table : Program 3 11 l) : Code :=
  scan (termBody table) ;; closeInto 16 21

abbrev blockBody {l : ℕ} (table : Program 3 11 l) : Code :=
  appendCapturedRecord 17 ;; scan (groupBody table) ;;
    closeInto 21 17 ;; closeInto 17 18

/-- The whole packing controller. The only parameter is the actual fixed
table-source instruction table; every outer traversal and byte writer is here. -/
abbrev command {l : ℕ} (table : Program 3 11 l) : Code :=
  scan (blockBody table) ;; pushBit 18 false ;; transfer 18 0 ;; reset

abbrev program {l : ℕ} (table : Program 3 11 l) :
    Program 3 22 (StructuredCalls.size (command table) + 1) :=
  StructuredCalls.compiled (command table) 0 0

theorem tablePorts_injective : Function.Injective tablePorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [tablePorts]

end SubexponentialSAT.SubexpBlockAssembly

end OAI.Algorithms
