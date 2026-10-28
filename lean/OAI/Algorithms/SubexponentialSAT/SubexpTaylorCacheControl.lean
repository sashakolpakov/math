import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorRow
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-! Fixed control for an incidence-major, coordinate-major Taylor cache.
The reusable row table is a framed list of framed coordinate-row lists.
Each innermost payload is a complete flat dense polynomial. The scalar
node is held on port 78 throughout the traversal. -/

namespace SubexponentialSAT.SubexpTaylorCacheControl

open BitProgram StructuredCalls

def rowRegs : Fin 8 ↪ Fin 14 := ⟨Fin.castAdd 6, Fin.castAdd_injective _ _⟩
def rowStacks : Fin 90 ↪ Fin 112 := ⟨Fin.castAdd 22, Fin.castAdd_injective _ _⟩
def writerRegs : Fin 5 ↪ Fin 14 := ⟨Fin.castAdd 9, Fin.castAdd_injective _ _⟩
def writerStacks : Fin 6 ↪ Fin 112 := ⟨![0,109,1,110,2,3], by decide⟩

def coordinatePorts : RecordPrograms.Ports 14 112 :=
  ⟨8,9,10,105,87, by decide, by decide, by decide, by decide⟩

def incidencePorts : RecordPrograms.Ports 14 112 :=
  ⟨11,12,13,103,104, by decide, by decide, by decide, by decide⟩

abbrev atom (a : StructuredProgram.Atom 14 112) : Cmd 14 112 := .base (.atom a)

abbrev transfer (src dst : Fin 112) : Cmd 14 112 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 14) 1)

abbrev writeRecord : Cmd 14 112 :=
  .call (ProgramLinking.liftProgram (SubexpArgumentProgram.writer true) writerRegs writerStacks)

abbrev runRow : Cmd 14 112 :=
  .call (ProgramLinking.liftProgram SubexpTaylorRow.program rowRegs rowStacks)

/-- The count master is copied once per row. The generated row cache is
framed and appended to the reversed coordinate-output accumulator. -/
abbrev coordinateCallback : Cmd 14 112 :=
  .seq (.call (StackRoutines.copyProgram 101 88 0 (0 : Fin 14) 1))
    (.seq runRow (.seq (transfer 89 109) (.seq writeRecord (transfer 110 106))))

abbrev finishList (reversed output : Fin 112) : Cmd 14 112 :=
  .seq (atom (.set 0 false)) (.seq (atom (.push reversed 0)) (transfer reversed output))

abbrev coordinates : Cmd 14 112 :=
  .seq (RecordPrograms.iterate coordinatePorts coordinateCallback) (finishList 106 107)

/-- The incidence parser returns reversed bytes of the coordinate-row list.
Its transfer restores that inner list before the coordinate traversal. -/
abbrev incidenceCallback : Cmd 14 112 :=
  .seq (transfer 104 105)
    (.seq coordinates (.seq (transfer 107 109) (.seq writeRecord (transfer 110 108))))

/-- Masters 100 (complete dense row table) and 101 (requested Taylor count)
are preserved. The incidence/coordinate/coefficient cache is returned on102. -/
abbrev command : Cmd 14 112 :=
  .seq (.call (StackRoutines.copyProgram 100 103 0 (0 : Fin 14) 1))
    (.seq (RecordPrograms.iterate incidencePorts incidenceCallback) (finishList 108 102))

abbrev program : Program 14 112 (size command + 1) := compiled command 100 102

/-- Concrete table representation used in the input and output contracts. -/
def encodeRows {C : Type*} (encode : C → List Bool) (rows : List (List (List C))) : List Bool :=
  Encoding.encodeList
    (fun coordinateRows => Encoding.encodeList (fun P => P.flatMap encode) coordinateRows) rows

def encodeCache {C : Type*} (encode : C → List Bool) (rows : List (List (List C))) : List Bool :=
  Encoding.encodeList
    (fun coordinateRows => Encoding.encodeList (Encoding.encodeList encode) coordinateRows) rows

end SubexponentialSAT.SubexpTaylorCacheControl

end OAI.Algorithms
