import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramRawLoop
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-! Direct table adapter: raw clause-reference rows to deduplicated scope rows.
The original source table and all decoding parameters remain on their tapes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

def flags (rf : Fin 11 → Bool) (v p f : Bool) : Fin 11 → Bool := fun i =>
  if i=8 then v else if i=9 then p else if i=10 then f else rf i

@[simp] theorem flags_idem (rf : Fin 11 → Bool) (v p f : Bool) :
    flags (flags rf v p f) v p f=flags rf v p f := by
  funext i
  by_cases h8 : i=8 <;> by_cases h9 : i=9 <;> by_cases h10 : i=10 <;>
    simp [flags,h8,h9,h10]

def reverseRegisters : Fin 3 → Fin 11 := ![8,9,10]
def reverseStacks : Fin 4 → Fin 49 := ![48,45,46,47]
theorem reverseRegisters_injective : Function.Injective reverseRegisters := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverse : Cmd 11 49 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks)

private theorem embed_reverse (rf : Fin 11 → Bool) (v p f : Bool)
    (width modulus master shape source output pay oldSource oldOut : List Bool) :
    embedState reverseRegisters reverseStacks (state rf width modulus master shape oldSource [] oldOut)
      (SubexpNormalizeProgram.filterState v p f source [] output pay) =
        state (flags rf v p f) width modulus master shape output pay source := by
  apply embedState_eq_of_ports _ _ _ _ _ reverseRegisters_injective reverseStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i≠8 := fun h => hi ⟨0,h.symm⟩
    have h9 : i≠9 := fun h => hi ⟨1,h.symm⟩
    have h10 : i≠10 := fun h => hi ⟨2,h.symm⟩
    simp [state,data,flags,h8,h9,h10]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h48 : i≠48 := fun h => hi ⟨0,h.symm⟩
    have h46 : i≠46 := fun h => hi ⟨2,h.symm⟩
    have h47 : i≠47 := fun h => hi ⟨3,h.symm⟩
    simp [state,data,h48,h46,h47]

theorem reverse_eval (rf : Fin 11 → Bool) (width modulus master shape : List Bool)
    (records : List (List Bool)) :
    ∃ n ≤ 10*(Encoding.encodeList id records).length,
      Eval reverse n
        (state (flags rf false true false) width modulus master shape [false] [] (Encoding.encodeList id records))
        (state (flags rf false true false) width modulus master shape (Encoding.encodeList id records.reverse) [] []) := by
  let a := state (flags rf false true false) width modulus master shape [false] [] (Encoding.encodeList id records)
  let z := SubexpNormalizeProgram.filterState false true false [] [] (Encoding.encodeList id records.reverse) []
  have ha : restrictState reverseRegisters reverseStacks a=
      SubexpNormalizeProgram.filterState false true false (Encoding.encodeList id records) [] [false] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] [] false true false
  obtain ⟨n,hn,he⟩ := lifted_call SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks
    reverseRegisters_injective reverseStacks_injective a z (10*(Encoding.encodeList id records).length)
    (by simpa [ha, z, Encoding.encodeList] using h)
  exact ⟨n,hn,by simpa [a,z,embed_reverse,flags_idem,reverse] using he⟩

theorem appendScopes_encoded (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : Rows clauses.length) (acc : List (List Bool)) :
    appendScopes (clauses := clauses) t d codes rows (Encoding.encodeList id acc)=
      Encoding.encodeList id ((rows.map (scopeBytes (clauses := clauses) t d codes)).reverse++acc) := by
  induction rows generalizing acc with
  | nil => simp [appendScopes]
  | cons row rows ih =>
      change appendScopes (clauses := clauses) t d codes rows (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes row)
        (Encoding.encodeList id acc))=_
      change appendScopes (clauses := clauses) t d codes rows (Encoding.encodeList id (scopeBytes (clauses := clauses) t d codes row::acc))=_
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem state_flags (rf : Fin 11 → Bool) (width modulus master shape src out : List Bool) (v p f : Bool) :
    RecordPrograms.state ports (state rf width modulus master shape [] [] out) v p f src []=
      state (flags rf v p f) width modulus master shape src [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,state,data,flags]
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,state,data]

abbrev initializeCmd : Cmd 11 49 := SubexponentialSAT.Subexp.TupleProgram.pushConst 48 8 false
abbrev seed : Cmd 11 49 := SubexponentialSAT.Subexp.TupleProgram.pushConst 46 8 false

theorem initialize_eval (width modulus master shape src : List Bool) :
    Eval initializeCmd 2 (state zeroRegs width modulus master shape src [] [])
      (state zeroRegs width modulus master shape src [] [false]) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (48 : Fin 49) (8 : Fin 11) false
    (state zeroRegs width modulus master shape src [] [])
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [state,data,zeroRegs]
  · funext i; fin_cases i <;> simp [state,data]

theorem seed_eval (rf : Fin 11 → Bool) (width modulus master shape out : List Bool) :
    Eval seed 2 (state (flags rf false true false) width modulus master shape [] [] out)
      (state (flags rf false true false) width modulus master shape [false] [] out) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (46 : Fin 49) (8 : Fin 11) false
    (state (flags rf false true false) width modulus master shape [] [] out)
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [state,data,flags]
  · funext i; fin_cases i <;> simp [state,data]

abbrev command : Cmd 11 49 := .seq initializeCmd (.seq iterate (.seq seed reverse))
def program := compiled command 46 46

def inputBits {m : ℕ} (b : ℕ) (rows : Rows m) := Encoding.encodeList id (rows.map (rowBits b))
def scopeBits (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : Rows clauses.length) :=
  Encoding.encodeList id (rows.map (scopeBytes (clauses := clauses) t d codes))
def cost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (rows : Rows clauses.length) :=
  8+loopCost t d b modulus clauses codes rows+10*(scopeBits (clauses := clauses) t d codes rows).length

theorem program_runsIn (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (width modulus shape : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn program (cost t d b modulus clauses codes rows)
      ((state zeroRegs width modulus (Encoding.encodeList id clauses) shape (inputBits b rows) [] []).withPC (some program.entry))
      ((state rf width modulus (Encoding.encodeList id clauses) shape (scopeBits (clauses := clauses) t d codes rows) [] []).withPC none) := by
  have hi := initialize_eval width modulus (Encoding.encodeList id clauses) shape (inputBits b rows)
  obtain ⟨ni,hni,rf,hei⟩ := iterate_eval t d ht b hb clauses codes hc rows hbound zeroRegs
    width modulus shape [false] hw hm hshape
  rw [state_flags,state_flags] at hei
  have hz : flags zeroRegs false false false=zeroRegs := by funext i; simp [flags,zeroRegs]
  rw [hz] at hei
  have ha := appendScopes_encoded t d codes rows []
  simp only [Encoding.encodeList,List.append_nil] at ha
  rw [ha] at hei
  have hs := seed_eval rf width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList id (rows.map (scopeBytes (clauses := clauses) t d codes)).reverse)
  obtain ⟨nr,hnr,her⟩ := reverse_eval rf width modulus (Encoding.encodeList id clauses) shape
    (rows.map (scopeBytes (clauses := clauses) t d codes)).reverse
  simp only [List.reverse_reverse] at her
  have hlen : (Encoding.encodeList id (rows.map (scopeBytes (clauses := clauses) t d codes)).reverse).length=
      (scopeBits (clauses := clauses) t d codes rows).length := ExecLiteralDedupProgram.encoded_reverse_length _
  rw [hlen] at hnr
  refine ⟨flags rf false true false,2+(ni+(2+nr))+1,by unfold cost; omega,?_⟩
  exact compiled_halt_trace (hi.seq (hei.seq (hs.seq her))) 46 46

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
