import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCode

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls SubexponentialSAT.BinaryArithmetic

def indexWidth (d : State 8 64) : ℕ :=
  (d.stacks 18).length+(d.stacks 3).length+(d.stacks 14).length+2

theorem indexArithmetic_eval (d : State 8 64)
    (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[]) :
    ∃ n rf product idx, Eval indexArithmetic n d
      ⟨rf,Function.update (Function.update d.stacks 20 product) 21 idx⟩ ∧
      BinaryArithmetic.toNat idx=BinaryArithmetic.toNat (d.stacks 18)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) ∧
      product.length ≤ indexWidth d ∧ idx.length ≤ indexWidth d ∧
      n ≤ 200*(indexWidth d)^2 := by
  have hv0 : Valid (arithmeticPorts 0) d := ⟨h20,hw⟩
  obtain ⟨t0,r0,w0,he0,hv0',hl0,ht0⟩ := multiplyAt_eval (arithmeticPorts 0) d hv0
  let a : State 8 64 := ⟨r0,Function.update d.stacks 20 w0⟩
  have hv1 : Valid (arithmeticPorts 1) a := by
    constructor
    · simpa [a,arithmeticPorts] using h21
    · intro i
      have hi : arithmeticWork i≠20 := (arithmeticPorts 0).work_ne_out i
      simpa [a,arithmeticPorts,hi] using hw i
  obtain ⟨t1,r1,w1,he1,hv1',hl1,ht1⟩ := addAt_eval (arithmeticPorts 1) a hv1
  have hval : BinaryArithmetic.toNat w1=BinaryArithmetic.toNat (d.stacks 18)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) := by
    simpa [a,arithmeticPorts,hv0'] using hv1'
  have hl0' : w0.length ≤ (d.stacks 18).length+(d.stacks 3).length+1 := by
    simpa [arithmeticPorts] using hl0
  have hl1' : w1.length ≤ w0.length+(d.stacks 14).length+1 := by
    simpa [a,arithmeticPorts] using hl1
  have hwidth0 : w0.length ≤ indexWidth d := by dsimp [indexWidth]; omega
  have hwidth1 : w1.length ≤ indexWidth d := by dsimp [indexWidth]; omega
  have ht0' : t0 ≤ 100*(indexWidth d)^2 := by
    apply ht0.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp [arithmeticPorts,indexWidth] ; omega
  have ht1' : t1 ≤ 100*(indexWidth d)^2 := by
    have hb : w0.length+(d.stacks 14).length+1 ≤ indexWidth d := by
      dsimp [indexWidth]
      omega
    have hh : t1 ≤ 100*(w0.length+(d.stacks 14).length+1)^2 := by
      simpa [a,arithmeticPorts] using ht1
    exact hh.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hb 2))
  exact ⟨t0+t1,r1,w0,w1,he0.seq he1,hval,hwidth0,hwidth1,by omega⟩

theorem low8_injective : Function.Injective low8 := Fin.castAdd_injective _ _

theorem index_eval (d : Data) (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[]) :
    ∃ n rf product idx, Eval (liftArithmetic indexArithmetic) n d
      ⟨rf,Function.update (Function.update d.stacks 20 product) 21 idx⟩ ∧
      BinaryArithmetic.toNat idx=BinaryArithmetic.toNat (d.stacks 18)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) ∧
      product.length ≤ indexWidth (projectState low8 id d) ∧
      idx.length ≤ indexWidth (projectState low8 id d) ∧
      n ≤ 200*(indexWidth (projectState low8 id d))^2+1 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  obtain ⟨n,rr,product,idx,he,hvalue,hproduct,hidx,hcost⟩ :=
    indexArithmetic_eval (projectState low8 id d) h20 h21 hw
  let small : State 8 64 := ⟨rr,Function.update (Function.update d.stacks 20 product) 21 idx⟩
  let out := embedState low8 id d small
  have he' := eval_liftCommand_from_state indexArithmetic 0 0 low8 id d
    low8_injective Function.injective_id he
  have hout : out=⟨out.regs,Function.update (Function.update d.stacks 20 product) 21 idx⟩ := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    exact Function.injective_id.extend_apply _ _ i
  change Eval (liftArithmetic indexArithmetic) (n+1) d out at he'
  rw [hout] at he'
  refine ⟨n+1,out.regs,product,idx,he',hvalue,hproduct,hidx,by omega,?_⟩
  intro i hi
  apply embedState_register_frame low8 id d small i
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  have hjlt := j.isLt
  dsimp [low8] at hh
  omega

theorem slotArithmetic_eval (d : Data) (h23 : d.stacks 23=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[]) :
    ∃ n rf word, Eval (liftArithmetic (addAt (arithmeticPorts 2))) n d
      ⟨rf,Function.update d.stacks 23 word⟩ ∧
      BinaryArithmetic.toNat word=BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (d.stacks 22) ∧
      word.length ≤ (d.stacks 21).length+(d.stacks 22).length+1 ∧
      n ≤ 100*((d.stacks 21).length+(d.stacks 22).length+1)^2+1 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  let a := projectState low8 id d
  have hv : Valid (arithmeticPorts 2) a := ⟨h23,hw⟩
  obtain ⟨n,rr,word,he,hval,hlen,hcost⟩ := addAt_eval (arithmeticPorts 2) a hv
  let small : State 8 64 := ⟨rr,Function.update d.stacks 23 word⟩
  let out := embedState low8 id d small
  have he' := eval_liftCommand_from_state (addAt (arithmeticPorts 2)) 0 0 low8 id d
    low8_injective Function.injective_id he
  have hout : out=⟨out.regs,Function.update d.stacks 23 word⟩ := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    exact Function.injective_id.extend_apply _ _ i
  change Eval (liftArithmetic (addAt (arithmeticPorts 2))) (n+1) d out at he'
  rw [hout] at he'
  refine ⟨n+1,out.regs,word,he',?_,?_,?_,?_⟩
  · simpa [a,arithmeticPorts,projectState] using hval
  · simpa [a,arithmeticPorts,projectState] using hlen
  · have hh : n ≤ 100*((d.stacks 21).length+(d.stacks 22).length+1)^2 := by
      simpa [a,arithmeticPorts,projectState] using hcost
    omega
  · intro i hi
    apply embedState_register_frame low8 id d small i
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    have hjlt := j.isLt
    dsimp [low8] at hh
    omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
