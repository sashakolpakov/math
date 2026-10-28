import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgramLog
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectTermination
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashInputs

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/

namespace SubexponentialSAT.SqrtLog.HashParametersProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

def inputWords (n m B : List Bool) : Words :=
  ![n,m,B,[],[],[],[],[],[],[],[],[],[],[],[]]

private theorem time_bound {t a W : ℕ} (ht : t ≤ 100*a^2)
    (ha : a ≤ 100*W) : t ≤ 1000000*W^2 := by
  calc
    t ≤ 100*a^2 := ht
    _ ≤ 100*(100*W)^2 := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left ha 2)
    _ = 1000000*W^2 := by ring

abbrev command : Cmd 8 22 :=
  .seq (copyClause) <|
  .seq (logCall) <|
  .seq (loadCmd 4 ([true,true] : List Bool)) <|
  .seq (loadCmd 5 ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool)) <|
  .seq (loadCmd 11 ([true] : List Bool)) <|
  .seq (multiplyCmd 2 2 6 (by decide) (by decide)) <|
  .seq (multiplyCmd 3 3 7 (by decide) (by decide)) <|
  .seq (multiplyCmd 6 7 8 (by decide) (by decide)) <|
  .seq (multiplyCmd 5 8 9 (by decide) (by decide)) <|
  .seq (addCmd 0 3 10 (by decide) (by decide)) <|
  .seq (addCmd 10 11 12 (by decide) (by decide)) <|
  .seq (addCmd 12 12 13 (by decide) (by decide)) <|
  multiplyCmd 1 4 14 (by decide) (by decide)

def width (n m B : List Bool) : ℕ := n.length + m.length + B.length + 1

theorem command_eval (regs : Regs) (n m B : List Bool) (hm : BinaryArithmetic.toNat m ≠ 0) :
    ∃ t rf output, Eval command t (state regs (inputWords n m B)) (state rf output) ∧
      BinaryArithmetic.toNat (output 14) = 3 * BinaryArithmetic.toNat m ∧
      BinaryArithmetic.toNat (output 9) = SparseCode.distanceDenom (BinaryArithmetic.toNat m) (BinaryArithmetic.toNat B) ∧
      BinaryArithmetic.toNat (output 13) = HashSelect.loopCap (BinaryArithmetic.toNat n) (BinaryArithmetic.toNat m) ∧
      (∀ i, (output i).length ≤ 100 * width n m B) ∧
      t ≤ 100000000 * (width n m B)^2 := by
  have len3 : ([true,true] : List Bool).length = 2 := by decide
  have len20000 : ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool).length = 15 := by decide
  have len1 : ([true] : List Bool).length = 1 := by decide
  have val20000 : BinaryArithmetic.toNat ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool) = 20000 := by decide
  have val3 : BinaryArithmetic.toNat ([true,true] : List Bool) = 3 := by decide
  have val1 : BinaryArithmetic.toNat ([true] : List Bool) = 1 := by decide
  let w0 := inputWords n m B
  have h0 := copyClause_eval regs w0 (by simp [w0,inputWords])
  let r0 := readRegs regs 0 1 none
  let w1 := Function.update w0 3 (w0 1)
  obtain ⟨tl,rl,vl,hl,hvl,hll,htl⟩ := logCall_eval r0 w1
  let w2 := Function.update w1 3 vl
  obtain ⟨r3,h3⟩ := load_eval rl w2 4 ([true,true] : List Bool) (by simp [w0,w1,w2,inputWords])
  let w3 := Function.update w2 4 ([true,true] : List Bool)
  obtain ⟨r4,h4⟩ := load_eval r3 w3 5 ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool) (by simp [w0,w1,w2,w3,inputWords])
  let w4 := Function.update w3 5 ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool)
  obtain ⟨r5,h5⟩ := load_eval r4 w4 11 ([true] : List Bool) (by simp [w0,w1,w2,w3,w4,inputWords])
  let w5 := Function.update w4 11 ([true] : List Bool)
  obtain ⟨t6,r6,v6,h6,hv6,hl6,ht6⟩ := multiply_eval r5 w5 2 2 6
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,inputWords])
  let w6 := Function.update w5 6 v6
  obtain ⟨t7,r7,v7,h7,hv7,hl7,ht7⟩ := multiply_eval r6 w6 3 3 7
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,inputWords])
  let w7 := Function.update w6 7 v7
  obtain ⟨t8,r8,v8,h8,hv8,hl8,ht8⟩ := multiply_eval r7 w7 6 7 8
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,inputWords])
  let w8 := Function.update w7 8 v8
  obtain ⟨t9,r9,v9,h9,hv9,hl9,ht9⟩ := multiply_eval r8 w8 5 8 9
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,inputWords])
  let w9 := Function.update w8 9 v9
  obtain ⟨t10,r10,v10,h10,hv10,hl10,ht10⟩ := add_eval r9 w9 0 3 10
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,inputWords])
  let w10 := Function.update w9 10 v10
  obtain ⟨t11,r11,v11,h11,hv11,hl11,ht11⟩ := add_eval r10 w10 10 11 12
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,inputWords])
  let w11 := Function.update w10 12 v11
  obtain ⟨t12,r12,v12,h12,hv12,hl12,ht12⟩ := add_eval r11 w11 12 12 13
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,inputWords])
  let w12 := Function.update w11 13 v12
  obtain ⟨t13,r13,v13,h13,hv13,hl13,ht13⟩ := multiply_eval r12 w12 1 4 14
    (by decide) (by decide) (by simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords])
  let w13 := Function.update w12 14 v13
  refine ⟨(7*(w0 1).length+5)+((tl)+((2*([true,true] : List Bool).length)+((2*([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool).length)+((2*([true] : List Bool).length)+((t6)+((t7)+((t8)+((t9)+((t10)+((t11)+((t12)+(t13)))))))))))),r13,w13,?_,?_,?_,?_,?_,?_⟩
  · exact h0.seq (hl.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13))))))))))))
  · simp only [w13,Function.update_self]
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,val1,val3,val20000] at hvl hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13
    rw [hv13]
    omega
  · simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,inputWords]
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,val1,val3,val20000] at hvl hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13
    rw [hv9,hv8,hv7,hv6,hvl]
    dsimp [SparseCode.distanceDenom]
    ring
  · simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,inputWords]
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,val1,val3,val20000] at hvl hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13
    rw [hv12,hv11,hv10,hvl]
    rw [HashSelect.loopCap,LeafParametersProgram.size_eq_log2_add_one hm]
    simp only [SparseCode.logSize,Nat.log2_eq_log_two]
    omega
  · intro i
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3,len20000,len1] at hll hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 htl ht6 ht7 ht8 ht9 ht10 ht11 ht12 ht13
    fin_cases i <;> simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,inputWords,len3,len20000,len1] <;> dsimp [width] <;> omega
  ·
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3,len20000,len1] at hll hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 htl ht6 ht7 ht8 ht9 ht10 ht11 ht12 ht13
    let W := width n m B
    have hW : 1 ≤ W := by dsimp [W,width]; omega
    have hb6 : (w5 2).length + (w5 2).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,inputWords] at hb6
    have hc6 := time_bound ht6 hb6
    have hb7 : (w6 3).length + (w6 3).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,inputWords] at hb7
    have hc7 := time_bound ht7 hb7
    have hb8 : (w7 6).length + (w7 7).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,inputWords] at hb8
    have hc8 := time_bound ht8 hb8
    have hb9 : (w8 5).length + (w8 8).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,inputWords,len20000]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,inputWords,len20000] at hb9
    have hc9 := time_bound ht9 hb9
    have hb10 : (w9 0).length + (w9 3).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,inputWords] at hb10
    have hc10 := time_bound ht10 hb10
    have hb11 : (w10 10).length + (w10 11).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,inputWords,len1]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,inputWords,len1] at hb11
    have hc11 := time_bound ht11 hb11
    have hb12 : (w11 12).length + (w11 12).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,inputWords]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,inputWords] at hb12
    have hc12 := time_bound ht12 hb12
    have hb13 : (w12 1).length + (w12 4).length + 1 ≤ 100*W := by
      simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3]; dsimp [W,width]; omega
    simp [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,inputWords,len3] at hb13
    have hc13 := time_bound ht13 hb13
    have hlog : (m.length+1)^2 ≤ W^2 := by
      apply Nat.pow_le_pow_left
      dsimp [W,width]
      omega
    have hcl : tl ≤ 36*W^2 := htl.trans (Nat.mul_le_mul_left 36 hlog)
    have hml : m.length ≤ W := by dsimp [W,width]; omega
    have hcopy : 7*m.length+41 ≤ 100*W^2 := by
      nlinarith only [hml,hW]
    change _ ≤ 100000000*W^2
    simp only [len3,len20000,len1]
    change 7*m.length+5 + (tl + (2*2 + (2*15 + (2*1 +
      (t6 + (t7 + (t8 + (t9 + (t10 + (t11 + (t12 + t13))))))))))) ≤ _
    omega

end SubexponentialSAT.SqrtLog.HashParametersProgram


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := State 16 44

def registers : Fin 8 → Fin 16 := Fin.castAdd 8
def stackMap (i : Fin 22) : Fin 44 := ⟨17+i.val,by omega⟩
def work : List (Fin 44) := List.ofFn stackMap
def inputs : List (Fin 44 × Fin 44) := [(14,17),(15,18),(16,19)]
def outputs : List (Fin 44 × Fin 44) := [(31,0),(26,5),(30,6)]

def prepared (a : Data) : Data := prepareState 39 work inputs a

def coreProgram := compiled HashParametersProgram.command 0 14

abbrev command : Cmd 16 44 := isolated coreProgram registers stackMap 39 work inputs outputs

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem stackMap_injective : Function.Injective stackMap := by
  intro i j h; apply Fin.ext
  have := congrArg Fin.val h
  dsimp [stackMap] at this
  omega

theorem work_mem (i : Fin 44) : i ∈ work ↔ 17 ≤ i.val ∧ i.val < 39 := by
  simp only [work,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩; dsimp [stackMap]; have := j.isLt; omega
  · intro hi; exact ⟨⟨i.val-17,by omega⟩,Fin.ext (by dsimp [stackMap]; omega)⟩

theorem inputs_good : ∀ p ∈ inputs,
    p.1 ≠ p.2 ∧ p.1 ≠ (39 : Fin 44) ∧ 39 ≠ p.2 := by
  intro p hp; simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> decide

theorem outputs_good : ∀ p ∈ outputs,
    p.1 ≠ p.2 ∧ p.1 ≠ (39 : Fin 44) ∧ 39 ≠ p.2 := by
  intro p hp; simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> decide

theorem prepared_project (a : Data) :
    project registers stackMap (prepared a) =
      SubexpBlockParameterProgram.state ((prepared a).regs ∘ registers)
        (HashParametersProgram.inputWords (a.stacks 14) (a.stacks 15) (a.stacks 16)) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp +decide [prepared,prepareState,beforeCopies,copyManyState,inputs,copyState,
        StackRoutines.copyStacks,resetMany_stacks,clearMany_stacks,stackMap,HashParametersProgram.inputWords,Fin.reduceFinMk]

/-- Assertion notation for the returned frame; the executable object is command. -/
noncomputable def returned (a : Data) (out : State 8 22) : Data :=
  finishState work outputs (embedState registers stackMap (prepared a) out)

theorem returned_frame (a : Data) (out : State 8 22) (i : Fin 44)
    (hw : i ∉ work) (ht : i ≠ 39)
    (h0 : i ≠ 0) (h5 : i ≠ 5) (h6 : i ≠ 6) :
    (returned a out).stacks i = a.stacks i := by
  rw [returned,finish_frame]
  · rw [embedState_stack_frame]
    · apply prepare_frame _ _ _ _ _ ht hw
      intro p hp
      simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl
      all_goals intro he; apply hw; rw [he]; rw [work_mem]; decide
    · rintro ⟨j,hj⟩
      apply hw
      rw [← hj]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · exact hw
  · intro p hp
    simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact h0
    · exact h5
    · exact h6

theorem returned_value (a : Data) (out : State 8 22)
    (p : Fin 44 × Fin 44) (hp : p ∈ outputs) :
    (returned a out).stacks p.2 = (embedState registers stackMap (prepared a) out).stacks p.1 := by
  refine finish_value work outputs _ (by decide) ?_ p hp ?_
  · intro q hq z hz
    simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hq hz
    rcases hq with rfl|rfl|rfl <;> rcases hz with rfl|rfl|rfl <;> decide
  · simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> (rw [work_mem]; decide)

theorem returned_values (a : Data) (out : State 8 22) :
    (returned a out).stacks 0 = out.stacks 14 ∧
    (returned a out).stacks 5 = out.stacks 9 ∧
    (returned a out).stacks 6 = out.stacks 13 := by
  have h0 := returned_value a out (31,0) (by simp [outputs])
  have h5 := returned_value a out (26,5) (by simp [outputs])
  have h6 := returned_value a out (30,6) (by simp [outputs])
  have e0 := embedState_stack registers stackMap (prepared a) out stackMap_injective 14
  have e5 := embedState_stack registers stackMap (prepared a) out stackMap_injective 9
  have e6 := embedState_stack registers stackMap (prepared a) out stackMap_injective 13
  exact ⟨h0.trans e0,h5.trans e5,h6.trans e6⟩

/-- No generic semantic callback is used: the only invoked program is the
fixed HashParametersProgram.command defined in the preceding module. -/
theorem command_eval (a : Data) (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ t rf output,
      let out := SubexpBlockParameterProgram.state rf output
      Eval command (prepareCost 39 work inputs a +
        (t+1+finishCost work outputs (embedState registers stackMap (prepared a) out)))
        a (returned a out) ∧
      BinaryArithmetic.toNat ((returned a out).stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat ((returned a out).stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat ((returned a out).stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) ∧
      (∀ i, (output i).length ≤ 100*HashParametersProgram.width (a.stacks 14) (a.stacks 15) (a.stacks 16)) ∧
      t ≤ 100000000*(HashParametersProgram.width (a.stacks 14) (a.stacks 15) (a.stacks 16))^2 := by
  obtain ⟨t,rf,output,he,h0,h5,h6,hl,ht⟩ := HashParametersProgram.command_eval
    ((prepared a).regs ∘ registers) (a.stacks 14) (a.stacks 15) (a.stacks 16) hm
  let out := SubexpBlockParameterProgram.state rf output
  have tr := compiled_halt_trace he 0 14
  have tr' : Trace coreProgram (t+1)
      ((project registers stackMap (prepared a)).withPC (some coreProgram.entry))
      (out.withPC none) := by
    rw [prepared_project]
    exact tr
  have run := isolated_eval coreProgram registers stackMap registers_injective stackMap_injective
    39 work inputs outputs a out inputs_good outputs_good
    (by rintro ⟨j,hj⟩; have := congrArg Fin.val hj; have := j.isLt; dsimp [stackMap] at *; omega)
    tr'
  have hv := returned_values a out
  refine ⟨t,rf,output,run,?_,?_,?_,hl,ht⟩
  · rw [hv.1]; exact h0
  · rw [hv.2.1]; exact h5
  · rw [hv.2.2]; exact h6

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Polynomial step budget for the complete physical parameter setup. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

theorem inputs_separated : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp hq
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> decide

theorem outputs_separated : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [outputs,List.mem_cons,List.mem_nil_iff,or_false] at hp hq
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> decide

theorem prepared_wordBound (a : Data) (L : ℕ) (ha : WordBound L a) :
    WordBound L (prepared a) := by
  apply prepare_wordBound 39 work inputs a L (by decide) _ inputs_separated ha
  intro p hp
  simp only [inputs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> (rw [work_mem]; decide)

theorem command_bounded (a : Data) (L : ℕ) (ha : WordBound L a)
    (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ cost b, Eval command cost a b ∧ cost ≤ 10000000000*(L+1)^2 ∧
      BinaryArithmetic.toNat (b.stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat (b.stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat (b.stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) ∧
      (∀ i, i ∉ work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 → b.stacks i = a.stacks i) ∧
      (∀ i ∈ work, b.stacks i = []) := by
  obtain ⟨t,rf,output,he,h0,h5,h6,hl,ht⟩ := command_eval a hm
  let out := SubexpBlockParameterProgram.state rf output
  let mid := embedState registers stackMap (prepared a) out
  let W := HashParametersProgram.width (a.stacks 14) (a.stacks 15) (a.stacks 16)
  have hW : W ≤ 4*(L+1) := by
    have h14 := ha 14
    have h15 := ha 15
    have h16 := ha 16
    dsimp [W,HashParametersProgram.width]
    omega
  have hLC : L ≤ 400*(L+1) := by omega
  have hp : WordBound (400*(L+1)) (prepared a) :=
    fun i => (prepared_wordBound a L ha i).trans hLC
  have ho : WordBound (400*(L+1)) out := by
    intro i
    dsimp [out,SubexpBlockParameterProgram.state]
    split
    · exact (hl _).trans (by change 100*W ≤ _; omega)
    · simp
  have hmid : WordBound (400*(L+1)) mid :=
    embedState_wordBound registers stackMap (prepared a) out _ stackMap_injective hp ho
  have hprep := prepareCost_le 39 work inputs a L inputs_separated ha
  have hfinish := finishCost_le work outputs mid (400*(L+1))
    (by decide) outputs_separated hmid
  have hpow := Nat.pow_le_pow_left hW 2
  have hcost : prepareCost 39 work inputs a + (t+1+finishCost work outputs mid)
      ≤ 10000000000*(L+1)^2 := by
    simp only [work,List.length_ofFn,inputs,outputs,List.length_cons,List.length_nil] at hprep hfinish
    change t ≤ 100000000*W^2 at ht
    simp only [work,inputs,outputs]
    nlinarith
  refine ⟨_,returned a out,he,hcost,h0,h5,h6,?_,?_⟩
  · exact returned_frame a out
  · intro i hi
    exact finish_empty work outputs mid i hi

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Exported fixed program and the selector's actual fourteen-port interface. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

def selectorRegisters : Fin 10 → Fin 16 := Fin.castAdd 6
def selectorStacks : Fin 14 → Fin 44 := Fin.castAdd 30

def selectorState (a : Data) : State 10 14 := projectState selectorRegisters selectorStacks a

def ReadyInput (a : Data) : Prop := Execution.HashInputs.Ready (selectorState a)

def program := compiled command 0 6

theorem command_ready_eval (a : Data) (L : ℕ) (ha : WordBound L a) (hr : ReadyInput a)
    (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ t ≤ 10000000000*(L+1)^2, ∃ b, Eval command t a b ∧
      Execution.HashInputs.Ready (selectorState b) ∧
      BinaryArithmetic.toNat (b.stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat (b.stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat (b.stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) ∧
      b.stacks 9 = a.stacks 9 ∧
      (∀ i, i ∉ work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 → b.stacks i = a.stacks i) := by
  obtain ⟨t,b,he,ht,h0,h5,h6,hframe,hclean⟩ := command_bounded a L ha hm
  refine ⟨t,ht,b,he,?_,h0,h5,h6,?_,hframe⟩
  · intro i hi0 hi5 hi6 hi9
    have hw : selectorStacks i ∉ work := by
      rw [work_mem]
      have := i.isLt
      change ¬ (17 ≤ i.val ∧ i.val < 39)
      omega
    have hh := hframe (selectorStacks i) hw (by
        intro h
        have hv := congrArg (fun x : Fin 44 => x.val) h
        change i.val=39 at hv
        have := i.isLt
        omega)
      (by intro h; apply hi0; exact Fin.ext (show i.val=0 from congrArg (fun x : Fin 44 => x.val) h))
      (by intro h; apply hi5; exact Fin.ext (show i.val=5 from congrArg (fun x : Fin 44 => x.val) h))
      (by intro h; apply hi6; exact Fin.ext (show i.val=6 from congrArg (fun x : Fin 44 => x.val) h))
    change b.stacks (selectorStacks i) = []
    rw [hh]
    exact hr i hi0 hi5 hi6 hi9
  · exact hframe 9 (by rw [work_mem]; decide) (by decide) (by decide) (by decide) (by decide)

theorem program_runs (a : Data) (L : ℕ) (ha : WordBound L a) (hr : ReadyInput a)
    (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ b, RunsIn program (10000000000*(L+1)^2+1)
        (a.withPC (some program.entry)) (b.withPC none) ∧
      Execution.HashInputs.Ready (selectorState b) ∧
      BinaryArithmetic.toNat (b.stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat (b.stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat (b.stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) ∧
      b.stacks 9 = a.stacks 9 ∧
      (∀ i, i ∉ work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 → b.stacks i = a.stacks i) := by
  obtain ⟨t,ht,b,he,hready,h0,h5,h6,h9,hframe⟩ := command_ready_eval a L ha hr hm
  exact ⟨b,⟨t+1,by omega,compiled_halt_trace he 0 6⟩,hready,h0,h5,h6,h9,hframe⟩

theorem program_primitive (a : Data) (L : ℕ) (ha : WordBound L a) (hr : ReadyInput a)
    (hm : BinaryArithmetic.toNat (a.stacks 15) ≠ 0) :
    ∃ b, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (10000000000*(L+1)^2+1))
      (primitiveCfg program (a.withPC (some program.entry)))
      (primitiveCfg program (b.withPC none)) ∧
      Execution.HashInputs.Ready (selectorState b) ∧
      BinaryArithmetic.toNat (b.stacks 0) = 3*BinaryArithmetic.toNat (a.stacks 15) ∧
      BinaryArithmetic.toNat (b.stacks 5) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks 15)) (BinaryArithmetic.toNat (a.stacks 16)) ∧
      BinaryArithmetic.toNat (b.stacks 6) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks 14)) (BinaryArithmetic.toNat (a.stacks 15)) := by
  obtain ⟨b,hb,hready,h0,h5,h6,_⟩ := program_runs a L ha hr hm
  exact ⟨b,primitive_execution program hb,hready,h0,h5,h6⟩

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

end OAI.Algorithms
