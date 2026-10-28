import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramAppend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCounter

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def emitted (d : Data) : List Bool :=
  if d.regs 7 then
    (SubexpLiftRing.fixedBits (d.stacks 5).length
      (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13
  else d.stacks 13

def finishedStacks (d : Data) : Fin 64 → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update
      (Function.update d.stacks 13 (emitted d)) 18 []) 20 []) 21 []) 14
    (CounterPrograms.ripple true (d.stacks 14))

def finishCost (d : Data) : ℕ := appendCost d+
  2*((d.stacks 18).length+(d.stacks 20).length+(d.stacks 21).length)+
  8*(d.stacks 14).length+20

theorem finishPort_eval (d : Data)
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h41 : d.stacks 41=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[])
    (hv : d.regs 7=true →
      BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) < 2^(d.stacks 5).length) :
    ∃ n rf, Eval finishPort n d ⟨rf,finishedStacks d⟩ ∧
      n ≤ finishCost d ∧ (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  have branch : ∃ n0 r0, Eval (.ite 7 appendSlot (.base .skip)) n0 d
      ⟨r0,Function.update d.stacks 13 (emitted d)⟩ ∧ n0 ≤ appendCost d+1 ∧
      (∀ i : Fin 16, 8 ≤ i.val → r0 i=d.regs i) := by
    cases hg : d.regs 7 with
    | false =>
      refine ⟨1,d.regs,?_,by omega,by intros; rfl⟩
      have he : (⟨d.regs,Function.update d.stacks 13 (emitted d)⟩ : Data)=d := by
        cases d with | mk regs stk => simp_all [emitted,Function.update_eq_self]
      rw [he]
      exact Eval.ite_false hg (.base (.skip d))
    | true =>
      obtain ⟨n0,r0,e0,b0,f0⟩ := appendSlot_eval d h22 h23 h24 h25 hw (hv hg)
      exact ⟨n0+1,r0,by simpa only [emitted,hg,ite_true] using Eval.ite_true hg e0,by omega,f0⟩
  obtain ⟨n0,r0,e0,b0,f0⟩ := branch
  let d0 : Data := ⟨r0,Function.update d.stacks 13 (emitted d)⟩
  let d1 := cleared 18 d0
  let d2 := cleared 20 d1
  let d3 := cleared 21 d2
  have e1 := clear_eval 18 d0
  have e2 := clear_eval 20 d1
  have e3 := clear_eval 21 d2
  have h41' : d3.stacks 41=[] := by simp [d3,d2,d1,d0,cleared,h41]
  have ei := increment_eval d3 14 (by decide) h41'
  let result := incremented d3 14 (by decide)
  have hout : result=⟨result.regs,finishedStacks d⟩ := by
    apply congrArg (StructuredProgram.State.mk result.regs)
    change result.stacks=finishedStacks d
    rw [show result.stacks=Function.update d3.stacks 14
      (CounterPrograms.ripple true (d3.stacks 14)) from
      incremented_stacks d3 14 (by decide) h41']
    simp [finishedStacks,d3,d2,d1,d0,cleared]
  let n := n0+(2*(d0.stacks 18).length+3+(2*(d1.stacks 20).length+3+
    (2*(d2.stacks 21).length+3+(CounterPrograms.rippleCost true (d3.stacks 14)+1))))
  have he : Eval finishPort n d result := e0.seq (e1.seq (e2.seq (e3.seq ei)))
  refine ⟨n,result.regs,by rw [←hout]; exact he,?_,?_⟩
  · have hi := CounterPrograms.rippleCost_le true (d3.stacks 14)
    simp only [d3,d2,d1,d0,cleared,Function.update_noteq (by decide : (14 : Fin 64)≠21),
      Function.update_noteq (by decide : (14 : Fin 64)≠20),
      Function.update_noteq (by decide : (14 : Fin 64)≠18),
      Function.update_noteq (by decide : (14 : Fin 64)≠13)] at hi
    dsimp [n]
    simp [d3,d2,d1,d0,cleared,finishCost] ; omega
  · intro i hi
    exact (incremented_register d3 14 (by decide) i (by omega)).trans
      ((cleared_register 21 d2 i (by omega)).trans
        ((cleared_register 20 d1 i (by omega)).trans
          ((cleared_register 18 d0 i (by omega)).trans (f0 i hi))))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
