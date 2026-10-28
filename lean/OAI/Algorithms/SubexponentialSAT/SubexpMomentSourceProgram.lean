import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWeightDescriptorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpKernelService
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceFraming
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Current-X source construction from an unweighted template

The template stores canonical Fp point banks, support lists, and prepared
factor rows.  It stores no weights and no postfix code. Every invocation
copies the reusable template, gathers the current exponent at each support,
computes each weight, builds each table's postfix source, and runs the r-fold
source constructor.  This file defines the actual finite control; execution
and quantitative refinements are supplied separately.
-/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

abbrev Word := List Bool
abbrev Data := State 8 63
abbrev Code := Cmd 8 63

structure Descriptor where
  bank : Word
  support : Word

structure Term where
  descriptor : Descriptor
  factors : List (List SubexpTableSource.Row)

structure Block where
  descriptor : Descriptor
  groups : List (List Term)

def encodeDescriptor (d : Descriptor) : Word := Encoding.frame d.bank ++ Encoding.frame d.support
def encodeTerm (t : Term) : Word := encodeDescriptor t.descriptor ++
  Encoding.frame (Encoding.encodeList SubexpTableSource.encodeRows t.factors)
def encodeGroup (ts : List Term) : Word := Encoding.encodeList encodeTerm ts
def encodeBlock (b : Block) : Word := encodeDescriptor b.descriptor ++
  Encoding.encodeList encodeGroup b.groups
def encodeTemplate (bs : List Block) : Word := Encoding.encodeList encodeBlock bs

def registers : Fin 3 → Fin 8 := Fin.castAdd 5
def assemblyPorts (i : Fin 22) : Fin 63 :=
  if i = 0 then 58 else if i = 1 then 59 else if i = 2 then 60 else ⟨i.val,by omega⟩

def descriptorPorts (i : Fin 38) : Fin 63 := match i.val with
  | 0 => 0 | 1 => 22 | 2 => 23 | 3 => 24 | 4 => 25 | 5 => 26
  | 6 => 27 | 7 => 28 | 8 => 29 | 9 => 19 | 10 => 30 | 11 => 31
  | 12 => 32 | 13 => 33 | 14 => 34 | 15 => 35 | 16 => 36 | 17 => 37
  | 18 => 38 | 19 => 39 | 20 => 40 | 21 => 41 | 22 => 42 | 23 => 43
  | 24 => 44 | 25 => 45 | 26 => 46 | 27 => 47 | 28 => 48 | 29 => 49
  | 30 => 50 | 31 => 51 | 32 => 52 | 33 => 53 | 34 => 54 | 35 => 55
  | 36 => 56 | _ => 57

def kernelPorts (i : Fin 24) : Fin 63 := match i.val with
  | 0 => 0 | 1 => 1 | 2 => 27 | 3 => 28 | 4 => 8 | 5 => 9
  | 6 => 10 | 7 => 11 | 8 => 12 | 9 => 13 | 10 => 14 | 11 => 15
  | 12 => 16 | 13 => 61 | 14 => 17 | 15 => 18 | 16 => 3 | 17 => 4
  | 18 => 59 | 19 => 60 | 20 => 58 | 21 => 5 | 22 => 6 | _ => 7

def base (c : SubexpBlockAssembly.Code) : Code :=
  liftCommand c 0 19 registers assemblyPorts

def transfer (src dst : Fin 63) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)
def clear (src : Fin 63) : Code := .call (StackRoutines.clearProgram src (0 : Fin 8) 1)

local infixr:60 " ;; " => Cmd.seq

/-- Move a forward payload through an empty reversal buffer, restoring its
original order at the destination. -/
def moveForward (src dst : Fin 63) : Code := transfer src 61 ;; transfer 61 dst

/-- Parse the two raw descriptor fields, compute the current exponent's
weight, and leave its raw polynomial literal on payload19. -/
def weightCapture : Code :=
  base SubexpBlockAssembly.capture ;; moveForward 19 22 ;;
  base SubexpBlockAssembly.capture ;; moveForward 19 29 ;;
  .call (ProgramLinking.liftProgram SubexpWeightDescriptorProgram.program id descriptorPorts) ;;
  clear 22

def weightFrame (dst : Fin 22) : Code :=
  weightCapture ;; base (SubexpBlockAssembly.appendFrame 19 dst) ;;
    base (SubexpBlockAssembly.clear 19)

def scan (body : Code) : Code :=
  base SubexpBlockAssembly.popTag ;;
    .while 0 (base SubexpBlockAssembly.unframe ;; body ;; base SubexpBlockAssembly.popTag)

def copyFactors : Code :=
  base SubexpBlockAssembly.capture ;; base (SubexpBlockAssembly.transfer 19 15)

/-- Frame an already complete payload. Its nested list already contains its
own terminator, so this operation emits no extra payload bit. -/
def packInto (src dst : Fin 22) : Code :=
  base (SubexpBlockAssembly.packComplete src dst)

def termBody : Code :=
  weightFrame 15 ;; copyFactors ;; packInto 15 16

def groupBody : Code := scan termBody ;; base (SubexpBlockAssembly.closeInto 16 21)

/-- Append a completed list directly to an enclosing payload. -/
def closeBare (src dst : Fin 22) : Code :=
  base (SubexpBlockAssembly.closeBare src dst)

def blockBody : Code :=
  weightFrame 17 ;; scan groupBody ;; closeBare 21 17 ;;
    packInto 17 18

/-- Master template62 is retained; work stream58 is regenerated for each X. -/
def prepareBlocks : Code :=
  .call (StackRoutines.copyProgram 62 58 2 (0 : Fin 8) 1) ;;
    scan blockBody ;; base (SubexpBlockAssembly.pushBit 18 false) ;;
    base (SubexpBlockAssembly.transfer 18 0) ;; base SubexpBlockAssembly.reset

def command : Code :=
  prepareBlocks ;;
    .call (ProgramLinking.liftProgram SubexpBlockAssembly.actualProgram registers assemblyPorts) ;;
    .call (ProgramLinking.liftProgram SubexpKernelService.program registers kernelPorts)

/-- Fixed finite control. Runtime data determines only the loop iterations. -/
def program := StructuredCalls.compiled command 0 1

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
