import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramRawTable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramMarkedStep

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := Marked.Data

def data (rf : Fin 11 → Bool) (width modulus master shape source out index flag : List Bool) : Data :=
  ⟨rf,fun j => if j=46 then source else Marked.tapes width modulus master shape out index flag [] [] [] j⟩

theorem data_empty (rf : Fin 11 → Bool) (width modulus master shape out index flag : List Bool) :
    data rf width modulus master shape [] out index flag=
      Marked.data rf width modulus master shape out index flag [] [] [] := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; by_cases hj : j=46 <;> simp [data,Marked.data,Marked.tapes,hj]

def lowStacks : Fin 49 → Fin 80 := Fin.castAdd 31
theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _
def rowsProgram := compiled RawTable.iterate 46 48
abbrev runRows : Cmd 11 80 := .call (ProgramLinking.liftProgram rowsProgram id lowStacks)
def reverseProgram := compiled RawTable.reverse 46 46
abbrev runReverse : Cmd 11 80 := .call (ProgramLinking.liftProgram reverseProgram id lowStacks)

private theorem restrict_data (rf : Fin 11 → Bool) (width modulus master shape source out index flag : List Bool) :
    restrictState id lowStacks (data rf width modulus master shape source out index flag)=
      RawTable.state rf width modulus master shape source [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; fin_cases j <;> rfl

private theorem embed_data (rf rr : Fin 11 → Bool)
    (width modulus master shape oldSource oldOut source out index flag : List Bool) :
    embedState id lowStacks (data rf width modulus master shape oldSource oldOut index flag)
      (RawTable.state rr width modulus master shape source [] out)=
        data rr width modulus master shape source out index flag := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lowStacks_injective
  · intro j; rfl
  · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h46 : j≠46 := fun h => hj ⟨46,h.symm⟩
    have h48 : j≠48 := fun h => hj ⟨48,h.symm⟩
    simp [data,Marked.tapes,h46,h48]

theorem runRows_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (width modulus shape out index flag : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ 4+RawTable.loopCost t d b modulus clauses codes rows, ∃ rf,
      Eval runRows n
        (data RawTable.zeroRegs width modulus (Encoding.encodeList id clauses) shape (RawTable.inputBits b rows) out index flag)
        (Marked.data rf width modulus (Encoding.encodeList id clauses) shape
          (RawTable.appendScopes (clauses := clauses) t d codes rows out) index flag [] [] []) := by
  obtain ⟨nr,hnr,rf,hr⟩ := RawTable.iterate_eval t d ht b hb clauses codes hc rows hbound RawTable.zeroRegs
    width modulus shape out hw hm hshape
  rw [RawTable.state_flags,RawTable.state_flags] at hr
  have hz : RawTable.flags RawTable.zeroRegs false false false=RawTable.zeroRegs := by
    funext j; simp [RawTable.flags,RawTable.zeroRegs]
  rw [hz] at hr
  let a := data RawTable.zeroRegs width modulus (Encoding.encodeList id clauses) shape (RawTable.inputBits b rows) out index flag
  let z := RawTable.state (RawTable.flags rf false true false) width modulus (Encoding.encodeList id clauses) shape [] []
    (RawTable.appendScopes (clauses := clauses) t d codes rows out)
  have hrun : RunsIn rowsProgram (4+RawTable.loopCost t d b modulus clauses codes rows)
      ((restrictState id lowStacks a).withPC (some rowsProgram.entry)) (z.withPC none) := by
    rw [restrict_data]
    exact ⟨nr+1,by omega,compiled_halt_trace hr 46 48⟩
  obtain ⟨n,hn,he⟩ := lifted_call rowsProgram id lowStacks Function.injective_id lowStacks_injective a z
    (4+RawTable.loopCost t d b modulus clauses codes rows) hrun
  exact ⟨n,hn,_,by simpa [runRows,a,z,embed_data,data_empty] using he⟩

theorem runReverse_eval (rf : Fin 11 → Bool) (width modulus master shape : List Bool)
    (records : List (List Bool))
    (h8 : rf 8=false) (h9 : rf 9=true) (h10 : rf 10=false) :
    ∃ n ≤ 10*(Encoding.encodeList id records).length+1,
      Eval runReverse n
        (data rf width modulus master shape [false] (Encoding.encodeList id records) [] [])
        (data rf width modulus master shape (Encoding.encodeList id records.reverse) [] [] []) := by
  have hf : RawTable.flags rf false true false=rf := by
    funext j
    by_cases h8j : j=8 <;> by_cases h9j : j=9 <;> by_cases h10j : j=10 <;>
      simp_all [RawTable.flags]
  obtain ⟨nr,hnr,hr⟩ := RawTable.reverse_eval rf width modulus master shape records
  rw [hf] at hr
  let a := data rf width modulus master shape [false] (Encoding.encodeList id records) [] []
  let z := RawTable.state rf width modulus master shape (Encoding.encodeList id records.reverse) [] []
  have hrun : RunsIn reverseProgram (10*(Encoding.encodeList id records).length+1)
      ((restrictState id lowStacks a).withPC (some reverseProgram.entry)) (z.withPC none) := by
    rw [restrict_data]
    exact ⟨nr+1,Nat.add_le_add_right hnr 1,compiled_halt_trace hr 46 46⟩
  obtain ⟨n,hn,he⟩ := lifted_call reverseProgram id lowStacks Function.injective_id lowStacks_injective a z
    (10*(Encoding.encodeList id records).length+1) hrun
  exact ⟨n,hn,by simpa [runReverse,a,z,embed_data] using he⟩

abbrev initializeCmd : Cmd 11 80 := SubexponentialSAT.Subexp.TupleProgram.pushConst 48 8 false
abbrev seed : Cmd 11 80 := SubexponentialSAT.Subexp.TupleProgram.pushConst 46 8 false

theorem initialize_eval (width modulus master shape source index flag : List Bool) :
    Eval initializeCmd 2 (data RawTable.zeroRegs width modulus master shape source [] index flag)
      (data RawTable.zeroRegs width modulus master shape source [false] index flag) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (48 : Fin 80) (8 : Fin 11) false
    (data RawTable.zeroRegs width modulus master shape source [] index flag)
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext j; fin_cases j <;> simp [data,RawTable.zeroRegs]
  · funext j; fin_cases j <;> simp [data,Marked.tapes]

theorem seed_eval (rf : Fin 11 → Bool) (width modulus master shape out : List Bool) (h8 : rf 8=false) :
    Eval seed 2 (Marked.data rf width modulus master shape out [] [] [] [] [])
      (data rf width modulus master shape [false] out [] []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (46 : Fin 80) (8 : Fin 11) false
    (Marked.data rf width modulus master shape out [] [] [] [] [])
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext j; by_cases hj : j=8 <;> simp_all [data,Marked.data,SubexponentialSAT.Subexp.TupleProgram.pushedState]
  · funext j; fin_cases j <;> simp [data,Marked.data,Marked.tapes]

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
