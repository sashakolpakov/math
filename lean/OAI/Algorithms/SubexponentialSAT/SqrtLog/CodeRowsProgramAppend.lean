import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramOffset
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramPaddingCall

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def appendCost (d : Data) : ℕ :=
  100*((d.stacks 21).length+(d.stacks 4).length+2)^2 +
    9*(d.stacks 4).length+11*(d.stacks 5).length+
    2*((d.stacks 21).length+(d.stacks 4).length+2)+30

theorem appendCost_le (d : Data) (W : ℕ)
    (h21 : (d.stacks 21).length ≤ W) (h4 : (d.stacks 4).length ≤ W)
    (h5 : (d.stacks 5).length ≤ W) : appendCost d ≤ 500*(W+1)^2 := by
  have hs : (d.stacks 21).length+(d.stacks 4).length+2 ≤ 2*(W+1) := by omega
  have hsq := Nat.pow_le_pow_left hs 2
  dsimp [appendCost]
  nlinarith

theorem appendSlot_eval (d : Data)
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[])
    (hv : BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) < 2^(d.stacks 5).length) :
    ∃ n rf, Eval appendSlot n d
      ⟨rf,Function.update d.stacks 13
        ((SubexpLiftRing.fixedBits (d.stacks 5).length
          (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13)⟩ ∧
      n ≤ appendCost d ∧ (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  obtain ⟨n0,r0,e0,b0,f0⟩ := coefficientOffset_eval d h22 h24
  let d0 : Data := ⟨r0,Function.update d.stacks 22 (offsetWord d)⟩
  have h23' : d0.stacks 23=[] := by simp [d0,h23]
  have hw' : ∀ i, d0.stacks (arithmeticWork i)=[] := by
    intro i
    have hi : arithmeticWork i≠22 := (arithmeticPorts 2).work_ne_right i
    simpa [d0,hi] using hw i
  obtain ⟨n1,r1,word,e1,v1,l1,b1,f1⟩ := slotArithmetic_eval d0 h23' hw'
  let d1 : Data := ⟨r1,Function.update d0.stacks 23 word⟩
  have h24' : d1.stacks 24=[] := by simp [d1,d0,h24]
  have ec := copy_eval 5 25 d1 (by decide) (by decide) (by decide) h24'
  let d2 := copied 5 25 d1
  have vw : BinaryArithmetic.toNat word=BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) := by
    simpa [d0] using v1
  have hv' : BinaryArithmetic.toNat (d2.stacks 23) < 2^(d2.stacks 25).length := by
    simpa [d2,copied,StackRoutines.copyStacks,d1,d0,h25,vw] using hv
  obtain ⟨r2,ep,fp⟩ := padding_call_eval d2 hv'
  let d3 : Data := ⟨r2,paddedStacks d2⟩
  have ez := clear_eval 23 d3
  let d4 := cleared 23 d3
  have eo := clear_eval 22 d4
  let result := cleared 22 d4
  have hout : result=⟨result.regs,Function.update d.stacks 13
      ((SubexpLiftRing.fixedBits (d.stacks 5).length
        (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13)⟩ := by
    apply congrArg (StructuredProgram.State.mk result.regs)
    funext i
    by_cases h13i : i=13
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h25,vw]
    by_cases h22i : i=22
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h22]
    by_cases h23i : i=23
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h23]
    by_cases h25i : i=25
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h25]
    simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,
      h13i,h22i,h23i,h25i]
  let cost := n0+(n1+(7*(d1.stacks 5).length+5+
    (4*(d2.stacks 25).length+3+(2*(d3.stacks 23).length+3+
      (2*(d4.stacks 22).length+3)))))
  have he : Eval appendSlot cost d result :=
    e0.seq (e1.seq (ec.seq (ep.seq (ez.seq eo))))
  refine ⟨cost,result.regs,by rw [←hout]; exact he,?_,?_⟩
  · have lo := offsetWord_length d
    have lw : word.length ≤ (d.stacks 21).length+(d.stacks 4).length+2 := by
      simp only [d0,Function.update_noteq (by decide : (21 : Fin 64)≠22),
        Function.update_same] at l1
      omega
    have ba : n1 ≤ 100*((d.stacks 21).length+(d.stacks 4).length+2)^2+1 := by
      apply b1.trans
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simp only [d0,Function.update_noteq (by decide : (21 : Fin 64)≠22),
        Function.update_same]
      omega
    have ldrop : (word.drop (d.stacks 5).length).length ≤ word.length := by
      simp only [List.length_drop]
      omega
    dsimp [cost]
    simp only [d1,d0,d2,copied,StackRoutines.copyStacks,d3,paddedStacks,d4,cleared,
      Function.update_same,Function.update_noteq (by decide : (5 : Fin 64)≠23),
      Function.update_noteq (by decide : (5 : Fin 64)≠22),
      Function.update_noteq (by decide : (25 : Fin 64)≠23),
      Function.update_noteq (by decide : (25 : Fin 64)≠22),
      Function.update_noteq (by decide : (23 : Fin 64)≠13),
      Function.update_noteq (by decide : (23 : Fin 64)≠25),
      Function.update_noteq (by decide : (22 : Fin 64)≠23),
      Function.update_noteq (by decide : (22 : Fin 64)≠13),
      Function.update_noteq (by decide : (22 : Fin 64)≠25),h25,List.append_nil]
    dsimp [appendCost]
    omega
  · intro i hi
    exact (cleared_register 22 d4 i (by omega)).trans
      ((cleared_register 23 d3 i (by omega)).trans
        ((fp i hi).trans ((copied_register 5 25 d1 i (by omega)).trans
          ((f1 i hi).trans (f0 i (by omega))))))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
