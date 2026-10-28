import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginQuadProgram
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentProgram
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-! Fixed control for origins in encounter order. The input is a preserved
Taylor cache: incidence, coordinate, then increasing Taylor degree. Only
the first coefficient of each nonempty shifted row is reduced to the
source field. The remaining degree records are consumed by an actual clear
loop. Output has the same incidence/coordinate order and source-width
quartet payloads. -/

namespace SubexponentialSAT.SubexpOriginControl

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

abbrev Data := State 14 32

def quadRegs : Fin 8 ↪ Fin 14 := ⟨Fin.castAdd 6, Fin.castAdd_injective _ _⟩
def quadPorts : Fin 20 ↪ Fin 32 := ⟨Fin.castAdd 12, Fin.castAdd_injective _ _⟩
def writerRegs : Fin 5 ↪ Fin 14 := ⟨Fin.castAdd 9, Fin.castAdd_injective _ _⟩
def writerPorts : Fin 6 ↪ Fin 32 := ⟨![0, 25, 1, 26, 2, 3], by decide⟩

def coordinatePorts : RecordPrograms.Ports 14 32 :=
  ⟨8, 9, 10, 17, 18, by decide, by decide, by decide, by decide⟩

def incidencePorts : RecordPrograms.Ports 14 32 :=
  ⟨11, 12, 13, 15, 16, by decide, by decide, by decide, by decide⟩

def degreePorts : RecordPrograms.Ports 14 32 :=
  ⟨0, 1, 2, 19, 20, by decide, by decide, by decide, by decide⟩

abbrev atom (a : StructuredProgram.Atom 14 32) : Cmd 14 32 := .base (.atom a)
abbrev transfer (src dst : Fin 32) : Cmd 14 32 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 14) 1)
abbrev clear (src : Fin 32) : Cmd 14 32 :=
  .call (StackRoutines.clearProgram src (0 : Fin 14) 1)

abbrev reduceQuad : Cmd 14 32 :=
  .call (ProgramLinking.liftProgram SubexpOriginQuadProgram.program quadRegs quadPorts)

abbrev writeRecord : Cmd 14 32 :=
  .call (ProgramLinking.liftProgram (SubexpArgumentProgram.writer true) writerRegs writerPorts)

/-- Extract the first shifted coefficient and discard its degree tail. -/
abbrev extractFirst : Cmd 14 32 :=
  .seq (transfer 18 19)
    (.seq (atom (.pop 19 0 1))
      (.seq (RecordPrograms.reader degreePorts) (.seq (clear 19) (transfer 20 8))))

abbrev coordinateCallback : Cmd 14 32 :=
  .seq extractFirst (.seq reduceQuad
    (.seq (transfer 8 25) (.seq writeRecord (transfer 26 21))))

abbrev finishList (reversed output : Fin 32) : Cmd 14 32 :=
  .seq (atom (.set 0 false)) (.seq (atom (.push reversed 0)) (transfer reversed output))

abbrev coordinates : Cmd 14 32 :=
  .seq (RecordPrograms.iterate coordinatePorts coordinateCallback) (finishList 21 22)

abbrev incidenceCallback : Cmd 14 32 :=
  .seq (transfer 16 17) (.seq coordinates
    (.seq (transfer 22 25) (.seq writeRecord (transfer 26 23))))

/-- Native masters: source modulus5, target word width10, source word
width11, Taylor cache14. Result24. All work is in0--26. -/
abbrev command : Cmd 14 32 :=
  .seq (.call (StackRoutines.copyProgram 14 15 0 (0 : Fin 14) 1))
    (.seq (RecordPrograms.iterate incidencePorts incidenceCallback) (finishList 23 24))

abbrev program : Program 14 32 (size command + 1) := compiled command 14 24

abbrev Row (B : ℕ) := Quad (Word B) × List (Quad (Word B))

def rowBytes {B : ℕ} (row : Row B) : List Bool :=
  Encoding.encodeList SubexpFlatLift.encode (row.1 :: row.2)

def inputBytes {B : ℕ} (rows : List (List (Row B))) : List Bool :=
  Encoding.encodeList (Encoding.encodeList rowBytes) rows

def outputBytes (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (width : List Bool) (hw : width.length = baseWidth p 1)
    {B : ℕ} (rows : List (List (Row B))) : List Bool :=
  Encoding.encodeList
    (fun incidence => Encoding.encodeList
      (fun row => SubexpFlatLift.encode (SubexpOriginResidue.quad p M width hw row.1)) incidence)
    rows

end SubexponentialSAT.SubexpOriginControl

end OAI.Algorithms
