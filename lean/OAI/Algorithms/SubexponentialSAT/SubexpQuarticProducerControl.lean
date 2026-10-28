import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticSharedTest
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticRecordLoad
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticBootstrap
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleProgram
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram

namespace OAI.Algorithms

/-!
# Fixed control of the selected-quartic byte producer

The input is the prime in little-endian binary on stack 34. The output is the
four selected coefficient words, concatenated on stack 33. Prime, word width,
candidate count, and divisor count are runtime data. The instruction table
contains only the fixed depths two and four and fixed workspace assignments.

Execution certification is separated from these control definitions. In
particular, defining this program alone is not a runtime or correctness claim.
-/

namespace SubexponentialSAT.SubexpQuarticProducerControl

open BitProgram StructuredCalls
open Subexp.BlockSearchProgram

abbrev Data := State 14 35
abbrev Command := Cmd 14 35

def sequence (commands : List Command) : Command := commands.foldr Cmd.seq (.base .skip)
def atom (a : StructuredProgram.Atom 14 35) : Command := .base (.atom a)
def clear (source : Fin 35) : Command := .call (StackRoutines.clearProgram source 0 1)
def copy (source destination : Fin 35) : Command :=
  .call (StackRoutines.copyProgram source destination 27 0 1)
def transfer (source destination : Fin 35) : Command :=
  .call (StackRoutines.transferProgram source destination 0 1)

def coreRegisters (i : Fin 8) : Fin 14 := Fin.castAdd 6 i
def coreStacks (i : Fin 23) : Fin 35 := Fin.castAdd 12 i

def linearTest : Command := .call (ProgramLinking.liftProgram
  SubexpQuarticSharedTest.linearProgram coreRegisters coreStacks)
def quadraticTest : Command := .call (ProgramLinking.liftProgram
  SubexpQuarticTestMachine.quadraticProgram coreRegisters coreStacks)

def loadWords (destinations : List (Fin 35)) : Command :=
  SubexpQuarticRecordLoad.load 31 32 22 30 0 1 destinations

def innerPorts : RecordPrograms.Ports 14 35 :=
  ⟨8, 9, 10, 23, 24, by decide, by decide, by decide, by decide⟩

def linearPorts : SavedPorts 14 35 where
  toPorts := innerPorts
  saved := 25
  temporary := 27
  saved_ne_source := by decide
  saved_ne_payload := by decide
  temporary_ne_source := by decide
  temporary_ne_payload := by decide
  saved_ne_temporary := by decide

def quadraticPorts : SavedPorts 14 35 where
  toPorts := innerPorts
  saved := 26
  temporary := 27
  saved_ne_source := by decide
  saved_ne_payload := by decide
  temporary_ne_source := by decide
  temporary_ne_payload := by decide
  saved_ne_temporary := by decide

def candidatePorts : RecordPrograms.Ports 14 35 :=
  ⟨11, 12, 13, 28, 29, by decide, by decide, by decide, by decide⟩

/-- The parser produces reversed payload bits; the transfer restores their
forward order before the runtime-width loader consumes them. -/
def finishInner : Command :=
  .seq (atom (.copy 10 2)) (.seq (atom (.set 8 false)) (atom (.set 9 true)))

def linearCallback : Command :=
  .seq (SubexpQuarticRecordLoad.readRecord 31 32 22 30 24 0 1 [4])
    (.seq linearTest finishInner)

def quadraticCallback : Command :=
  .seq (SubexpQuarticRecordLoad.readRecord 31 32 22 30 24 0 1 [4, 5])
    (.seq quadraticTest finishInner)

/-- Every attempted candidate is saved on output 33 before both divisor
lists are checked. First-success control retains exactly the first passing
candidate, matching QuarticSearch.coefficients. -/
def saveCandidate : Command :=
  .seq (clear 33) (.seq (copy 29 24) (transfer 29 33))

def loadCandidate : Command := .seq saveCandidate
  (SubexpQuarticRecordLoad.readRecord 31 32 22 30 24 0 1 [0, 1, 2, 3])

def testCandidate : Command :=
  .seq (savedAllCommand linearPorts linearCallback) (.seq (atom (.copy 13 10))
    (.seq (savedAllCommand quadraticPorts quadraticCallback) (.seq (atom (.band 13 13 10))
      (.seq (atom (.set 11 false)) (atom (.set 12 true))))))

def candidateCallback : Command := .seq loadCandidate testCandidate

def search : Command := RecordPrograms.iterate candidatePorts candidateCallback

def normalizerRegisters (i : Fin 3) : Fin 14 := Fin.castAdd 11 i
def normalizerStacks : Fin 3 → Fin 35 := ![34, 0, 1]
def normalizePrime : Command := .call (ProgramLinking.liftProgram
  CounterNormalizeProgram.program normalizerRegisters normalizerStacks)

def alphabetRegisters (i : Fin 6) : Fin 14 := Fin.castAdd 8 i
def alphabetStacks : Fin 6 → Fin 35 := ![34, 22, 0, 1, 2, 25]
def makeAlphabet : Command := .call (ProgramLinking.liftProgram
  SubexpAlphabetProgram.program alphabetRegisters alphabetStacks)

def tupleRegisters (i : Fin 10) : Fin 14 := Fin.castAdd 4 i
def tupleStacks (output : Fin 35) : Fin 9 → Fin 35 := ![output, 25, 0, 1, 2, 3, 4, 5, 6]
def makePairs : Command := .call (ProgramLinking.liftProgram
  SubexpOrderedTupleProgram.pairs tupleRegisters (tupleStacks 26))
def makeCandidates : Command := .call (ProgramLinking.liftProgram
  SubexpOrderedTupleProgram.quartics tupleRegisters (tupleStacks 28))

/-- The tuple generator leaves an empty-list marker in local stack five,
which is physical stack three. Clear it before the next initialization. -/
def prepare : Command := sequence
  [normalizePrime, copy 34 19, copy 34 31, makeAlphabet,
   makePairs, clear 3, makeCandidates, clear 3, SubexpQuarticBootstrap.command]

def cleanupPorts : List (Fin 35) := (List.finRange 35).filter (fun i => i != 33)
def cleanup : Command := BankRoutines.clearCmd 27 0 1 cleanupPorts

def command : Command := sequence [prepare, search, cleanup]
def program := compiled command 34 33

end SubexponentialSAT.SubexpQuarticProducerControl

end OAI.Algorithms
