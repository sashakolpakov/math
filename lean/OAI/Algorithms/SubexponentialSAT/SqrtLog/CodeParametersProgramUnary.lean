import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative
import OAI.Algorithms.SubexponentialSAT.SubexpGuardProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

/-- The minimal graph dimension is computed by one division and a binary size,
including the one-vertex case. No unbounded semantic search is needed by the
physical parameter program. -/
theorem dimensionFor_eq_size {m D : ℕ} (hm : 0 < m) (hD : 0 < D) :
    SparseCode.dimensionFor m D = Nat.size ((m-1)/D) := by
  apply Nat.le_antisymm
  · apply SparseCode.dimensionFor_le m hD
    have h := Nat.lt_size_self ((m-1)/D)
    have hh := (Nat.div_lt_iff_lt_mul hD).mp h
    rw [Nat.mul_comm] at hh
    omega
  · apply Nat.size_le.mpr
    apply (Nat.div_lt_iff_lt_mul hD).mpr
    have h := SparseCode.dimensionFor_spec m hD
    rw [Nat.mul_comm]
    omega

theorem dimension_eq_size {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    SparseCode.dimension m B = Nat.size ((m-1)/SparseCode.degree m B) :=
  dimensionFor_eq_size hm (SparseCode.degree_pos hm hB)

/-- A branch-free implementation of binary size using the existing positive
logarithm primitive. -/
theorem size_eq_log2_odd (z : ℕ) : Nat.size z = Nat.log2 (2*z+1) := by
  have ha := LeafParametersProgram.size_eq_log2_add_one (n := 2*z+1) (by omega)
  have hb : Nat.size (2*z+1) = Nat.size z+1 := by
    simpa [Nat.bit, Nat.two_mul] using
      (Nat.size_bit (b := true) (n := z) (by simp [Nat.bit]))
  omega

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

def minComparePorts : Fin 2 → Fin 77 := ![port 62,port 63]

abbrev minCommand : Cmd 8 77 :=
  .seq (copyCmd 0 62) <| .seq (copyCmd 8 63) <|
  .seq (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program id minComparePorts)) <|
  .ite 0 (copyCmd 0 9) (copyCmd 8 9)

theorem minCommand_eval (r : Regs) (w : Words)
    (h62 : w 62 = []) (h63 : w 63 = []) (h9 : w 9 = []) :
    ∃ t rf word, Eval minCommand t (state r w) (state rf (Function.update w 9 word))  ∧
      BinaryArithmetic.toNat word = min (BinaryArithmetic.toNat (w 0)) (BinaryArithmetic.toNat (w 8))  ∧
      word.length  ≤  (w 0).length+(w 8).length  ∧
      t  ≤  40*((w 0).length+(w 8).length+1) := by
  obtain ⟨r1,h1⟩ := copy_eval r w 0 62 (by decide) h62
  let w1 := Function.update w 62 (w 0)
  obtain ⟨r2,h2⟩ := copy_eval r1 w1 8 63 (by decide) (by simpa [w1] using h63)
  let w2 := Function.update w1 63 (w1 8)
  have hinj : Function.Injective minComparePorts := by decide
  obtain ⟨e,he,hflag,_,hframe,hclear⟩ := SubexpGuardProgram.compare_call id minComparePorts
    Function.injective_id hinj (state r2 w2)
  have ee : e = state e.regs w := by
    apply CounterForPrograms.data_ext (a := e) (b := state e.regs w) rfl
    funext i
    by_cases hi62 : i = port 62
    · subst i
      exact (hclear 0).trans (by simpa only [state_port] using h62.symm)
    by_cases hi63 : i = port 63
    · subst i
      exact (hclear 1).trans (by simpa only [state_port] using h63.symm)
    have hf := hframe i (by
      rintro ⟨j,hj⟩
      fin_cases j
      · exact hi62 hj.symm
      · exact hi63 hj.symm)
    rw [hf]
    have hv62 : i.val ≠ 62 := by intro h; apply hi62; exact Fin.ext h
    have hv63 : i.val ≠ 63 := by intro h; apply hi63; exact Fin.ext h
    simp [state,w2,w1,Function.update_apply,Fin.ext_iff,Fin.coe_ofNat_eq_mod,hv62,hv63]
  have hs0 : (state r2 w2).stacks (minComparePorts 0)=w 0 := by
    change (state r2 w2).stacks (port 62)=_
    rw [state_port]
    simp [w2,w1]
  have hs1 : (state r2 w2).stacks (minComparePorts 1)=w 8 := by
    change (state r2 w2).stacks (port 63)=_
    rw [state_port]
    simp [w2,w1]
  have hcmp : e.regs 0 = true ↔ BinaryArithmetic.toNat (w 0) < BinaryArithmetic.toNat (w 8) := by
    simpa only [hs0,hs1,id_eq] using hflag
  have hem : Eval (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program id minComparePorts))
      (10*max (w 0).length (w 8).length+6) (state r2 w2) (state e.regs w) := by
    rw [ee] at he
    simpa only [hs0,hs1] using he
  by_cases hlt : BinaryArithmetic.toNat (w 0) < BinaryArithmetic.toNat (w 8)
  · obtain ⟨rf,hf⟩ := copy_eval e.regs w 0 9 (by decide) h9
    refine ⟨7*(w 0).length+5 + (7*(w1 8).length+5 +
      (10*max (w 0).length (w 8).length+6 + (7*(w 0).length+5+1))),
      rf,w 0,?_,(Nat.min_eq_left hlt.le).symm,by omega,?_⟩
    · exact h1.seq (h2.seq (hem.seq (.ite_true (hcmp.mpr hlt) hf)))
    · simp only [w1,Function.update_of_ne (by decide : (8 : Fin 64)  ≠  62)]
      have hm := max_le (Nat.le_add_right (w 0).length (w 8).length)
        (Nat.le_add_left (w 8).length (w 0).length)
      omega
  · obtain ⟨rf,hf⟩ := copy_eval e.regs w 8 9 (by decide) h9
    refine ⟨7*(w 0).length+5 + (7*(w1 8).length+5 +
      (10*max (w 0).length (w 8).length+6 + (7*(w 8).length+5+1))),
      rf,w 8,?_,(Nat.min_eq_right (by omega)).symm,by omega,?_⟩
    · exact h1.seq (h2.seq (hem.seq (.ite_false (Bool.eq_false_iff.mpr (fun h => hlt (hcmp.mp h))) hf)))
    · simp only [w1,Function.update_of_ne (by decide : (8 : Fin 64)  ≠  62)]
      have hm := max_le (Nat.le_add_right (w 0).length (w 8).length)
        (Nat.le_add_left (w 8).length (w 0).length)
      omega

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank
open LeafParametersProgram.Circuit

def prefixCode : List Instr := [
  .copy 0 2 (by decide), .logSucc 2,
  .load 3 ([false,false,false,true,false,false,true,true] : List Bool),
  .mul 1 2 4 (by decide) (by decide),
  .mul 3 4 5 (by decide) (by decide),
  .mul 5 5 6 (by decide) (by decide),
  .load 7 ([false,false,false,true] : List Bool),
  .mul 7 6 22 (by decide) (by decide),
  .mul 22 2 8 (by decide) (by decide)]

def suffixCode : List Instr := [
  .mul 7 1 10 (by decide) (by decide),
  .quot 9 10 11 (by decide) (by decide), .addConst 11 1,
  .mul 11 9 12 (by decide) (by decide),
  .load 13 ([false,false,true,false,false,true,true] : List Bool),
  .mul 13 4 14 (by decide) (by decide),
  .quot 9 14 15 (by decide) (by decide), .addConst 15 1,
  .copy 0 16 (by decide), .pred 16,
  .quot 16 9 17 (by decide) (by decide),
  .add 17 17 18 (by decide) (by decide), .addConst 18 1, .logSucc 18, .pred 18,
  .mul 18 9 19 (by decide) (by decide),
  .load 20 ([false,true] : List Bool),
  .pow 20 18 21 (by decide) (by decide)]

def initialModel (m B ml Bl : ℕ) : Model where
  val i := if i=0 then m else if i=1 then B else 0
  len i := if i=0 then ml else if i=1 then Bl else 0

def prefixModel (m B ml Bl : ℕ) : Model := result prefixCode (initialModel m B ml Bl)

def middleModel (m B ml Bl : ℕ) : Model where
  val := Function.update (prefixModel m B ml Bl).val 9 (SparseCode.degree m B)
  len := Function.update (prefixModel m B ml Bl).len 9
    ((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8)

def finalModel (m B ml Bl : ℕ) : Model := result suffixCode (middleModel m B ml Bl)

abbrev command : Cmd 8 77 :=
  .seq (LeafParametersProgram.Circuit.program prefixCode)
    (.seq minCommand (LeafParametersProgram.Circuit.program suffixCode))

def runtimeBound (m B ml Bl : ℕ) : ℕ :=
  budget prefixCode (initialModel m B ml Bl) +
  (40*((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8+1)+
   budget suffixCode (middleModel m B ml Bl))

theorem prefix_values (m B ml Bl : ℕ) :
    (prefixModel m B ml Bl).val 0=m  ∧
    (prefixModel m B ml Bl).val 5=SparseCode.gapDenom m B  ∧
    (prefixModel m B ml Bl).val 8=SparseCode.degreeBound m B := by
  simp [prefixModel,prefixCode,result,next,output,value,initialModel,BinaryArithmetic.toNat,bitVal,SparseCode.gapDenom,SparseCode.degreeBound,
    SparseCode.logSize,Nat.log2_eq_log_two]
  ; ring_nf ; simp

theorem prefix_admissible (m B ml Bl : ℕ) :
    AdmissibleCode prefixCode (initialModel m B ml Bl) := by
  simp [prefixCode,AdmissibleCode,Admissible,next,output,lengthBound,initialModel]

theorem suffix_admissible {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    AdmissibleCode suffixCode (middleModel m B ml Bl) := by
  have hd := SparseCode.degree_pos hm hB
  simp [suffixCode,AdmissibleCode,Admissible,middleModel,prefixModel,prefixCode,
    result,next,output,value,lengthBound,initialModel,BinaryArithmetic.toNat,bitVal,hB,hd]


theorem final_values {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    (finalModel m B ml Bl).val 5=SparseCode.gapDenom m B  ∧
    (finalModel m B ml Bl).val 9=SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 11=SparseCode.localRows m B  ∧
    (finalModel m B ml Bl).val 12=SparseCode.localRows m B*SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 15=SparseCode.degree m B/(100*B*SparseCode.logSize m)+1  ∧
    (finalModel m B ml Bl).val 18=SparseCode.dimension m B  ∧
    (finalModel m B ml Bl).val 19=SparseCode.dimension m B*SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 21=2^SparseCode.dimension m B := by
  have hr := dimension_eq_size hm hB
  rw [size_eq_log2_odd] at hr
  have hr' : Nat.log 2 (((m-1)/SparseCode.degree m B)+((m-1)/SparseCode.degree m B)+1) =
      SparseCode.dimension m B := by
    simpa [Nat.two_mul,Nat.log2_eq_log_two] using hr.symm
  simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,result,next,output,
    value,initialModel,BinaryArithmetic.toNat,bitVal,SparseCode.gapDenom,SparseCode.localRows,
    SparseCode.logSize,Nat.log2_eq_log_two,Nat.mul_assoc,hr']

/-- The actual binary search words have length linear in the lengths of the
input metadata, independently of their numeric values. -/
theorem final_search_lengths (m B ml Bl : ℕ) :
    (finalModel m B ml Bl).len 5 = ml+Bl+11 ∧
    (finalModel m B ml Bl).len 9 = 4*ml+2*Bl+30 := by
  simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,result,next,
    output,lengthBound,initialModel]
  ; omega

/-- Execute the fixed arithmetic table and the concrete minimum comparator.
All copy, division, logarithm and exponentiation costs are included. -/
theorem command_eval {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (ml Bl : ℕ) (w : Words) (r : Regs) (hw : Shape (initialModel m B ml Bl) w) :
    ∃ t rf w', Eval command t (state r w) (state rf w')  ∧
      Shape (finalModel m B ml Bl) w'  ∧  t ≤ runtimeBound m B ml Bl := by
  obtain ⟨t1,r1,w1,h1,hs1,ht1⟩ := program_eval prefixCode (initialModel m B ml Bl)
    w r hw (prefix_admissible m B ml Bl)
  have hz (i : Fin 64) (hi : (prefixModel m B ml Bl).len i=0) : w1 i=[] := by
    have hh := hs1.2 i
    change (w1 i).length  ≤  (prefixModel m B ml Bl).len i at hh
    rw [hi] at hh
    exact List.length_eq_zero_iff.mp (by omega)
  have hzero (i : Fin 64) (hi : i=9  ∨  i=62  ∨  i=63) :
      (prefixModel m B ml Bl).len i=0 := by
    rcases hi with rfl|rfl|rfl <;>
      simp [prefixModel,prefixCode,result,next,output,lengthBound,initialModel]
  obtain ⟨t2,r2,v2,h2,hv2,hl2,ht2⟩ := minCommand_eval r1 w1
    (hz 62 (hzero _ (by simp))) (hz 63 (hzero _ (by simp))) (hz 9 (hzero _ (by simp)))
  let w2 := Function.update w1 9 v2
  have hs2 : Shape (middleModel m B ml Bl) w2 := by
    constructor
    · intro i
      by_cases hi : i=9
      · subst i
        simp only [w2,Function.update_self,middleModel]
        rw [hv2,hs1.1,hs1.1]
        exact congrArg₂ min (prefix_values m B ml Bl).1 (prefix_values m B ml Bl).2.2
      · simpa [w2,middleModel,prefixModel,hi] using hs1.1 i
    · intro i
      by_cases hi : i=9
      · subst i
        simp only [w2,Function.update_self,middleModel]
        exact hl2.trans (Nat.add_le_add (hs1.2 0) (hs1.2 8))
      · simpa [w2,middleModel,prefixModel,hi] using hs1.2 i
  obtain ⟨t3,r3,w3,h3,hs3,ht3⟩ := program_eval suffixCode (middleModel m B ml Bl)
    w2 r2 hs2 (suffix_admissible hm hB ml Bl)
  refine ⟨t1+(t2+t3),r3,w3,h1.seq (h2.seq h3),hs3,?_⟩
  have ht2' : t2 ≤ 40*((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8+1) :=
    ht2.trans (Nat.mul_le_mul_left 40 (by
      have h0 : (w1 0).length ≤ (prefixModel m B ml Bl).len 0 := hs1.2 0
      have h8 : (w1 8).length ≤ (prefixModel m B ml Bl).len 8 := hs1.2 8
      omega))
  exact Nat.add_le_add ht1 (Nat.add_le_add ht2' ht3)

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

def conversionPorts (o : Fin 64) : Fin 3 → Fin 77 :=
  ![port 62,port o,work 1 (by decide) 0]

abbrev conversion (o : Fin 64) : Cmd 8 77 :=
  liftCommand CounterConversions.unaryCmd 0 1 smallRegs (conversionPorts o)

theorem conversionPorts_injective (o : Fin 64) (ho : o ≠ 62) :
    Function.Injective (conversionPorts o) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [conversionPorts,port,work,Fin.ext_iff,Fin.coe_ofNat_eq_mod] <;> omega

abbrev unaryCopy (a o : Fin 64) : Cmd 8 77 := .seq (copyCmd a 62) (conversion o)

theorem unaryCopy_eval (r : Regs) (w : Words) (a o : Fin 64)
    (ha : a ≠ 62) (ho : o ≠ 62) (_hao : a ≠ o) (h62 : w 62=[]) (hout : w o=[]) :
    ∃ t rf, Eval (unaryCopy a o) t (state r w)
        (state rf (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true)))  ∧
      t ≤ 7*(w a).length+6+CounterConversions.coreBound (w a) := by
  obtain ⟨r1,h1⟩ := copy_eval r w a 62 (Ne.symm ha) h62
  let w1 := Function.update w 62 (w a)
  let d := state r1 w1
  let p := conversionPorts o
  have hp : Function.Injective p := conversionPorts_injective o ho
  let localState := projectState smallRegs p d
  have hwork : localState.stacks 2=[] := by
    change (state r1 w1).stacks (work 1 (by decide) 0)=[]
    exact state_work _ _ _ (by decide)
  obtain ⟨u,hu,hub⟩ := CounterConversions.unary_correct localState hwork
  let z := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (BinaryArithmetic.toNat (w a)) true)
  have hlocal : Eval CounterConversions.unaryCmd u localState z := by
    have hs : localState.stacks 0=w a := by
      change (state r1 w1).stacks (port 62)=_
      rw [state_port]
      simp [w1]
    have he : localState.stacks 1=[] := by
      change (state r1 w1).stacks (port o)=_
      rw [state_port]
      simp [w1,ho,hout]
    simpa only [hs,he,List.append_nil,CounterPrograms.value_eq_toNat] using hu
  let e := embedState smallRegs p d z
  have h2 : Eval (conversion o) (u+1) d e :=
    eval_liftCommand_from_state _ _ _ _ _ _ (Fin.castAdd_injective 3 5) hp hlocal
  have es : e = state e.regs (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true)) := by
    apply CounterForPrograms.data_ext (a := e)
      (b := state e.regs (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true))) rfl
    funext i
    by_cases hi62 : i=port 62
    · subst i
      have hh := embedState_stack smallRegs p d z hp 0
      change e.stacks (port 62)=[] at hh
      rw [state_port,Function.update_of_ne (Ne.symm ho)]
      exact hh.trans h62.symm
    by_cases hio : i=port o
    · subst i
      have hh := embedState_stack smallRegs p d z hp 1
      change e.stacks (port o)=List.replicate (BinaryArithmetic.toNat (w a)) true at hh
      simpa only [state_port,Function.update_self] using hh
    by_cases hiw : i=work 1 (by decide) 0
    · subst i
      have hh := embedState_stack smallRegs p d z hp 2
      change e.stacks (work 1 (by decide) 0)=[] at hh
      rw [state_work _ _ _ (by decide)]
      exact hh
    have hf := embedState_stack_frame smallRegs p d z i (by
      rintro ⟨j,hj⟩
      fin_cases j
      · exact hi62 hj.symm
      · exact hio hj.symm
      · exact hiw hj.symm)
    rw [hf]
    have hv62 : i.val ≠ 62 := by
      intro h
      apply hi62
      exact Fin.ext h
    have hvo : i.val ≠ o.val := by
      intro h
      apply hio
      exact Fin.ext h
    simp [d,w1,state,Function.update_apply,Fin.ext_iff,Fin.coe_ofNat_eq_mod,hv62,hvo]
  refine ⟨7*(w a).length+5+(u+1),e.regs,?_,?_⟩
  · rw [← es]
    exact h1.seq h2
  · have hs : localState.stacks 0=w a := by
      change (state r1 w1).stacks (port 62)=_
      rw [state_port]
      simp [w1]
    rw [hs] at hub
    omega

/-- Each pair is (binary source, unary destination). Binary source words are
retained. Destination slots24--30 and temporary slot62 start empty. -/
def unaryPairs : List (Fin 64 × Fin 64) :=
  [(9,24),(11,25),(12,26),(15,27),(18,28),(19,29),(21,30)]

abbrev unaryCommand : Cmd 8 77 :=
  .seq (unaryCopy 9 24) <| .seq (unaryCopy 11 25) <| .seq (unaryCopy 12 26) <|
  .seq (unaryCopy 15 27) <| .seq (unaryCopy 18 28) <| .seq (unaryCopy 19 29) <|
  unaryCopy 21 30

def unaryWords (w : Words) : Words :=
  unaryPairs.foldl (fun z p => Function.update z p.2 (List.replicate (BinaryArithmetic.toNat (w p.1)) true)) w

def unaryBudget (w : Words) : ℕ :=
  (unaryPairs.map (fun p => 7*(w p.1).length+6+CounterConversions.coreBound (w p.1))).sum

theorem unaryCommand_eval (r : Regs) (w : Words) (h62 : w 62=[])
    (h24 : w 24=[]) (h25 : w 25=[]) (h26 : w 26=[]) (h27 : w 27=[])
    (h28 : w 28=[]) (h29 : w 29=[]) (h30 : w 30=[]) :
    ∃ t rf, Eval unaryCommand t (state r w) (state rf (unaryWords w))  ∧  t ≤ unaryBudget w := by
  obtain ⟨t1,r1,he1,ht1⟩ := unaryCopy_eval r w 9 24
    (by decide) (by decide) (by decide) (by exact h62) (by exact h24)
  let w1 := Function.update w 24 (List.replicate (BinaryArithmetic.toNat (w 9)) true)
  obtain ⟨t2,r2,he2,ht2⟩ := unaryCopy_eval r1 w1 11 25
    (by decide) (by decide) (by decide) (by simpa [w1] using h62) (by simpa [w1] using h25)
  let w2 := Function.update w1 25 (List.replicate (BinaryArithmetic.toNat (w1 11)) true)
  obtain ⟨t3,r3,he3,ht3⟩ := unaryCopy_eval r2 w2 12 26
    (by decide) (by decide) (by decide) (by simpa [w1,w2] using h62) (by simpa [w1,w2] using h26)
  let w3 := Function.update w2 26 (List.replicate (BinaryArithmetic.toNat (w2 12)) true)
  obtain ⟨t4,r4,he4,ht4⟩ := unaryCopy_eval r3 w3 15 27
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3] using h62) (by simpa [w1,w2,w3] using h27)
  let w4 := Function.update w3 27 (List.replicate (BinaryArithmetic.toNat (w3 15)) true)
  obtain ⟨t5,r5,he5,ht5⟩ := unaryCopy_eval r4 w4 18 28
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3,w4] using h62) (by simpa [w1,w2,w3,w4] using h28)
  let w5 := Function.update w4 28 (List.replicate (BinaryArithmetic.toNat (w4 18)) true)
  obtain ⟨t6,r6,he6,ht6⟩ := unaryCopy_eval r5 w5 19 29
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3,w4,w5] using h62) (by simpa [w1,w2,w3,w4,w5] using h29)
  let w6 := Function.update w5 29 (List.replicate (BinaryArithmetic.toNat (w5 19)) true)
  obtain ⟨t7,r7,he7,ht7⟩ := unaryCopy_eval r6 w6 21 30
    (by decide) (by decide) (by decide) (by simpa [w1,w2,w3,w4,w5,w6] using h62) (by simpa [w1,w2,w3,w4,w5,w6] using h30)
  let w7 := Function.update w6 30 (List.replicate (BinaryArithmetic.toNat (w6 21)) true)
  refine ⟨t1+(t2+(t3+(t4+(t5+(t6+t7))))),r7,?_,?_⟩
  · have he := he1.seq (he2.seq (he3.seq (he4.seq (he5.seq (he6.seq he7)))))
    simpa [unaryCommand,unaryWords,unaryPairs,w1,w2,w3,w4,w5,w6,w7] using he
  · simp [w1,w2,w3,w4,w5,w6] at ht1 ht2 ht3 ht4 ht5 ht6 ht7
    simp only [unaryBudget,unaryPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega

def unaryModelBudget (z : LeafParametersProgram.Circuit.Model) : ℕ :=
  (unaryPairs.map (fun p =>
    7*z.len p.1+6+(2*z.val p.1+(z.val p.1+1)*(16*z.len p.1+16)+2*z.len p.1+6))).sum

theorem unaryBudget_le (z : LeafParametersProgram.Circuit.Model) (w : Words)
    (hs : LeafParametersProgram.Circuit.Shape z w) : unaryBudget w ≤ unaryModelBudget z := by
  have hb (a : Fin 64) : 7*(w a).length+6+CounterConversions.coreBound (w a)  ≤
      7*z.len a+6+(2*z.val a+(z.val a+1)*(16*z.len a+16)+2*z.len a+6) := by
    simp only [CounterConversions.coreBound,CounterPrograms.value_eq_toNat,hs.1]
    gcongr <;> exact hs.2 a
  have h9 := hb 9
  have h11 := hb 11
  have h12 := hb 12
  have h15 := hb 15
  have h18 := hb 18
  have h19 := hb 19
  have h21 := hb 21
  simp only [unaryBudget,unaryModelBudget,unaryPairs,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  omega

def binaryPorts : Fin 7 → Fin 64 := ![9,11,12,15,18,19,21]
def unaryPorts : Fin 7 → Fin 64 := ![24,25,26,27,28,29,30]
def parameterValues (m B : ℕ) : Fin 7 → ℕ :=
  ![SparseCode.degree m B,SparseCode.localRows m B,
    SparseCode.localRows m B*SparseCode.degree m B,
    SparseCode.degree m B/(100*B*SparseCode.logSize m)+1,
    SparseCode.dimension m B,SparseCode.dimension m B*SparseCode.degree m B,
    2^SparseCode.dimension m B]

/-- Unary materialization is paid by numeric value. All seven values are
polynomial in the original number of violation coordinates, even when B is
large. In particular the vertex count is not charged merely by bit length. -/
theorem parameterValues_le {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (j : Fin 7) :
    parameterValues m B j  ≤  2*(m+1)^2 := by
  have hD := SparseCode.degree_le m B
  have hDpos := SparseCode.degree_pos hm hB
  have ht : SparseCode.localRows m B ≤ m+1 := by
    unfold SparseCode.localRows
    have := Nat.div_le_self (SparseCode.degree m B) (8*B)
    omega
  have hd : SparseCode.degree m B/(100*B*SparseCode.logSize m)+1 ≤ m+1 := by
    have := Nat.div_le_self (SparseCode.degree m B) (100*B*SparseCode.logSize m)
    omega
  have hr : SparseCode.dimension m B ≤ m := by
    rw [dimension_eq_size hm hB]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans
      ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))
  have hN : 2^SparseCode.dimension m B ≤ 2*m := by
    calc
      _ = 2^SparseCode.dimension m B*1 := by simp
      _  ≤  2^SparseCode.dimension m B*SparseCode.degree m B :=
        Nat.mul_le_mul_left _ hDpos
      _  ≤  _ := (SparseCode.graph_edge_upper hm hB).le
  have htD := Nat.mul_le_mul ht hD
  have hrD := Nat.mul_le_mul hr hD
  fin_cases j <;> simp +decide [parameterValues,Fin.reduceFinMk] <;> nlinarith

abbrev fullCommand : Cmd 8 77 := .seq command unaryCommand

def fullBudget (m B ml Bl : ℕ) : ℕ :=
  runtimeBound m B ml Bl+unaryModelBudget (finalModel m B ml Bl)

theorem fullCommand_eval_with_lengths {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (r : Regs) (w : Words) (hs : LeafParametersProgram.Circuit.Shape (initialModel m B ml Bl) w) :
    ∃ t rf w', Eval fullCommand t (state r w) (state rf w')  ∧  t ≤ fullBudget m B ml Bl  ∧
      BinaryArithmetic.toNat (w' 0)=m  ∧  BinaryArithmetic.toNat (w' 5)=SparseCode.gapDenom m B  ∧
      (∀ j, BinaryArithmetic.toNat (w' (binaryPorts j))=parameterValues m B j)  ∧
      (∀ j, w' (unaryPorts j)=List.replicate (parameterValues m B j) true) ∧
      (w' 5).length ≤ ml+Bl+11 ∧ (w' 9).length ≤ 4*ml+2*Bl+30 := by
  obtain ⟨t1,r1,w1,h1,hs1,ht1⟩ := command_eval hm hB ml Bl w r hs
  have hz (i : Fin 64) (hi : i=62  ∨  (24 ≤ i.val  ∧  i.val ≤ 30)) : w1 i=[] := by
    have hlen : (finalModel m B ml Bl).len i=0 := by
      rcases hi with rfl|hi
      · simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,
          LeafParametersProgram.Circuit.result,LeafParametersProgram.Circuit.next,
          LeafParametersProgram.Circuit.output,LeafParametersProgram.Circuit.lengthBound,initialModel]
      · have hi' : i=24  ∨  i=25  ∨  i=26  ∨  i=27  ∨  i=28  ∨  i=29  ∨  i=30 := by omega
        rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,
            LeafParametersProgram.Circuit.result,LeafParametersProgram.Circuit.next,
            LeafParametersProgram.Circuit.output,LeafParametersProgram.Circuit.lengthBound,initialModel]
    have hh:=hs1.2 i
    rw [hlen] at hh
    exact List.length_eq_zero_iff.mp (by omega)
  obtain ⟨t2,r2,h2,ht2⟩ := unaryCommand_eval r1 w1 (hz 62 (by simp))
    (hz 24 (by decide)) (hz 25 (by decide)) (hz 26 (by decide)) (hz 27 (by decide))
    (hz 28 (by decide)) (hz 29 (by decide)) (hz 30 (by decide))
  have hv:=final_values hm hB ml Bl
  have hp (j : Fin 7) : BinaryArithmetic.toNat (w1 (binaryPorts j))=parameterValues m B j := by
    rw [hs1.1]
    fin_cases j
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2.1
    · exact hv.2.2.2.2.1
    · exact hv.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.2
  refine ⟨t1+t2,r2,unaryWords w1,h1.seq h2,
    Nat.add_le_add ht1 (ht2.trans (unaryBudget_le _ _ hs1)),?_,?_,?_,?_,?_,?_⟩
  · have hm0 : (finalModel m B ml Bl).val 0=m := by
      simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,
        LeafParametersProgram.Circuit.result,LeafParametersProgram.Circuit.next,
        LeafParametersProgram.Circuit.output,initialModel]
    simpa [unaryWords,unaryPairs] using (hs1.1 0).trans hm0
  · simpa [unaryWords,unaryPairs] using (hs1.1 5).trans hv.1
  · intro j
    have hf : unaryWords w1 (binaryPorts j)=w1 (binaryPorts j) := by
      fin_cases j <;> simp [unaryWords,unaryPairs,binaryPorts]
    rw [hf]
    exact hp j
  · intro j
    have hf : unaryWords w1 (unaryPorts j)=List.replicate (BinaryArithmetic.toNat (w1 (binaryPorts j))) true := by
      fin_cases j <;> simp [unaryWords,unaryPairs,binaryPorts,unaryPorts]
    rw [hf,hp j]
  · have hh := hs1.2 5
    rw [(final_search_lengths m B ml Bl).1] at hh
    simpa [unaryWords,unaryPairs] using hh
  · have hh := hs1.2 9
    rw [(final_search_lengths m B ml Bl).2] at hh
    simpa [unaryWords,unaryPairs] using hh

theorem fullCommand_eval {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (r : Regs) (w : Words) (hs : LeafParametersProgram.Circuit.Shape (initialModel m B ml Bl) w) :
    ∃ t rf w', Eval fullCommand t (state r w) (state rf w')  ∧  t ≤ fullBudget m B ml Bl  ∧
      BinaryArithmetic.toNat (w' 0)=m  ∧  BinaryArithmetic.toNat (w' 5)=SparseCode.gapDenom m B  ∧
      (∀ j, BinaryArithmetic.toNat (w' (binaryPorts j))=parameterValues m B j)  ∧
      (∀ j, w' (unaryPorts j)=List.replicate (parameterValues m B j) true) := by
  obtain ⟨t,rf,w',he,ht,hm0,hq,hbin,hunary,_,_⟩ :=
    fullCommand_eval_with_lengths hm hB ml Bl r w hs
  exact ⟨t,rf,w',he,ht,hm0,hq,hbin,hunary⟩

def program := compiled fullCommand 0 30

theorem program_runs {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (r : Regs) (w : Words) (hs : LeafParametersProgram.Circuit.Shape (initialModel m B ml Bl) w) :
    ∃ rf w', RunsIn program (fullBudget m B ml Bl+1)
      ((state r w).withPC (some program.entry)) ((state rf w').withPC none)  ∧
      BinaryArithmetic.toNat (w' 0)=m  ∧  BinaryArithmetic.toNat (w' 5)=SparseCode.gapDenom m B  ∧
      (∀ j, BinaryArithmetic.toNat (w' (binaryPorts j))=parameterValues m B j)  ∧
      (∀ j, w' (unaryPorts j)=List.replicate (parameterValues m B j) true) := by
  obtain ⟨t,rf,w',he,ht,hm0,hq,hbin,hunary⟩ := fullCommand_eval hm hB ml Bl r w hs
  exact ⟨rf,w',⟨t+1,by omega,compiled_halt_trace he 0 30⟩,hm0,hq,hbin,hunary⟩

theorem program_runs_with_lengths {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (r : Regs) (w : Words) (hs : LeafParametersProgram.Circuit.Shape (initialModel m B ml Bl) w) :
    ∃ rf w', RunsIn program (fullBudget m B ml Bl+1)
      ((state r w).withPC (some program.entry)) ((state rf w').withPC none) ∧
      BinaryArithmetic.toNat (w' 0)=m ∧ BinaryArithmetic.toNat (w' 5)=SparseCode.gapDenom m B ∧
      (∀ j, BinaryArithmetic.toNat (w' (binaryPorts j))=parameterValues m B j) ∧
      (∀ j, w' (unaryPorts j)=List.replicate (parameterValues m B j) true) ∧
      (w' 5).length ≤ ml+Bl+11 ∧ (w' 9).length ≤ 4*ml+2*Bl+30 := by
  obtain ⟨t,rf,w',he,ht,hm0,hq,hbin,hunary,hql,hDl⟩ :=
    fullCommand_eval_with_lengths hm hB ml Bl r w hs
  exact ⟨rf,w',⟨t+1,by omega,compiled_halt_trace he 0 30⟩,hm0,hq,hbin,hunary,hql,hDl⟩

theorem program_primitive {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (r : Regs) (w : Words) (hs : LeafParametersProgram.Circuit.Shape (initialModel m B ml Bl) w) :
    ∃ rf w', Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(fullBudget m B ml Bl+1))
      (primitiveCfg program ((state r w).withPC (some program.entry)))
      (primitiveCfg program ((state rf w').withPC none))  ∧
      BinaryArithmetic.toNat (w' 0)=m  ∧  BinaryArithmetic.toNat (w' 5)=SparseCode.gapDenom m B  ∧
      (∀ j, BinaryArithmetic.toNat (w' (binaryPorts j))=parameterValues m B j)  ∧
      (∀ j, w' (unaryPorts j)=List.replicate (parameterValues m B j) true) := by
  obtain ⟨rf,w',he,hm0,hq,hb,hu⟩ := program_runs hm hB ml Bl r w hs
  exact ⟨rf,w',BitProgram.primitive_execution program he,hm0,hq,hb,hu⟩

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
