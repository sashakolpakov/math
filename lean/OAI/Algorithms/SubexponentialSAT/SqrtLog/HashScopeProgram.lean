import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramLoop
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-! Complete native scope-table materialization from encoded weighted raw rows.
The output order agrees with the input row order. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Outer
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
def reverseStacks : Fin 4 → Fin 25 := ![24,21,22,23]
theorem reverseRegisters_injective : Function.Injective reverseRegisters := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverse : Cmd 11 25 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks)

private theorem embed_reverse (rf : Fin 11 → Bool) (v p f : Bool)
    (source output pay oldSource oldOut : List Bool) :
    embedState reverseRegisters reverseStacks (data rf [] [] oldSource [] oldOut)
      (SubexpNormalizeProgram.filterState v p f source [] output pay) =
        data (flags rf v p f) [] [] output pay source := by
  apply embedState_eq_of_ports _ _ _ _ _ reverseRegisters_injective reverseStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0,h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1,h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2,h.symm⟩
    simp [data,flags,h8,h9,h10]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h24 : i ≠ 24 := fun h => hi ⟨0,h.symm⟩
    have h22 : i ≠ 22 := fun h => hi ⟨2,h.symm⟩
    have h23 : i ≠ 23 := fun h => hi ⟨3,h.symm⟩
    simp [data,h24,h22,h23]

theorem reverse_eval (rf : Fin 11 → Bool) (records : List (List Bool)) :
    ∃ t ≤ 10*(Encoding.encodeList id records).length,
      Eval reverse t
        (data (flags rf false true false) [] [] [false] [] (Encoding.encodeList id records))
        (data (flags rf false true false) [] [] (Encoding.encodeList id records.reverse) [] []) := by
  let a := data (flags rf false true false) [] [] [false] [] (Encoding.encodeList id records)
  let b := SubexpNormalizeProgram.filterState false true false [] []
    (Encoding.encodeList id records.reverse) []
  have ha : restrictState reverseRegisters reverseStacks a =
      SubexpNormalizeProgram.filterState false true false (Encoding.encodeList id records) [] [false] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have ht := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] [] false true false
  have hb : b = SubexpNormalizeProgram.filterState false true false [] []
      (Encoding.encodeList id records.reverse) [] := rfl
  obtain ⟨t,hn,he⟩ := lifted_call SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters
    reverseStacks reverseRegisters_injective reverseStacks_injective a b
    (10*(Encoding.encodeList id records).length)
      (by rw [ha, hb]; simpa only [List.append_nil, Encoding.encodeList] using ht)
  refine ⟨t,hn,?_⟩
  simpa [a,b,embed_reverse,flags_idem,reverse] using he

theorem appendScopes_encoded (rows : Rows) (acc : List (List Bool)) :
    appendScopes rows (Encoding.encodeList id acc) =
      Encoding.encodeList id ((rows.map scopeBytes).reverse ++ acc) := by
  induction rows generalizing acc with
  | nil => simp [appendScopes]
  | cons row rows ih =>
      change appendScopes rows (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes row)
        (Encoding.encodeList id acc)) = _
      change appendScopes rows (Encoding.encodeList id (scopeBytes row :: acc)) = _
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem state_flags (rf : Fin 11 → Bool) (src out : List Bool) (v p f : Bool) :
    RecordPrograms.state ports (data rf [] [] [] [] out) v p f src [] =
      data (flags rf v p f) [] [] src [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data,flags]
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data]

abbrev initializeCmd : Cmd 11 25 := SubexponentialSAT.Subexp.TupleProgram.pushConst 24 8 false
abbrev seed : Cmd 11 25 := SubexponentialSAT.Subexp.TupleProgram.pushConst 22 8 false

theorem initialize_eval (src : List Bool) :
    Eval initializeCmd 2 (data zeroRegs [] [] src [] [])
      (data zeroRegs [] [] src [] [false]) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (24 : Fin 25) (8 : Fin 11) false
    (data zeroRegs [] [] src [] [])
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,zeroRegs]
  · funext i; fin_cases i <;> simp [data]

theorem seed_eval (rf : Fin 11 → Bool) (out : List Bool) :
    Eval seed 2 (data (flags rf false true false) [] [] [] [] out)
      (data (flags rf false true false) [] [] [false] [] out) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (22 : Fin 25) (8 : Fin 11) false
    (data (flags rf false true false) [] [] [] [] out)
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,flags]
  · funext i; fin_cases i <;> simp [data]

abbrev command : Cmd 11 25 := .seq initializeCmd (.seq iterate (.seq seed reverse))
def program := compiled command 22 22

def scopeBits (rows : Rows) : List Bool := Encoding.encodeList id (rows.map scopeBytes)
def inputBits (rows : Rows) : List Bool := Encoding.encodeList id (rows.map rowBits)
def cost (rows : Rows) : ℕ := 8+loopCost rows+10*(scopeBits rows).length

theorem program_runsIn (rows : Rows) :
    ∃ rf, RunsIn program (cost rows)
      ((data zeroRegs [] [] (inputBits rows) [] []).withPC (some program.entry))
      ((data rf [] [] (scopeBits rows) [] []).withPC none) := by
  have hi := initialize_eval (inputBits rows)
  obtain ⟨ti,hti,rf,he⟩ := iterate_eval rows zeroRegs [false]
  rw [state_flags,state_flags] at he
  have hz : flags zeroRegs false false false=zeroRegs := by funext i; simp [flags,zeroRegs]
  rw [hz] at he
  have ha := appendScopes_encoded rows []
  simp only [Encoding.encodeList,List.append_nil] at ha
  rw [ha] at he
  have hs := seed_eval rf (Encoding.encodeList id (rows.map scopeBytes).reverse)
  obtain ⟨tr,htr,hr⟩ := reverse_eval rf (rows.map scopeBytes).reverse
  simp only [List.reverse_reverse] at hr
  have hlen : (Encoding.encodeList id (rows.map scopeBytes).reverse).length = (scopeBits rows).length := by
    exact ExecLiteralDedupProgram.encoded_reverse_length _
  rw [hlen] at htr
  refine ⟨flags rf false true false,2+(ti+(2+tr))+1,by unfold cost; omega,?_⟩
  exact compiled_halt_trace (hi.seq (he.seq (hs.seq hr))) 22 22

theorem primitive_runsIn (rows : Rows) :
    ∃ rf, Computation.RunsIn (primitive program).step (primitiveOverhead program * cost rows)
      (primitiveCfg program ((data zeroRegs [] [] (inputBits rows) [] []).withPC (some program.entry)))
      (primitiveCfg program ((data rf [] [] (scopeBits rows) [] []).withPC none)) := by
  obtain ⟨rf,h⟩ := program_runsIn rows
  exact ⟨rf,primitive_execution program h⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.Outer

end OAI.Algorithms
