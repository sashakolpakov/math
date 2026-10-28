import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def offsetWord (d : Data) : List Bool :=
  if d.regs 9 then false::d.stacks 4 else if d.regs 8 then d.stacks 4 else []

theorem offsetWord_length (d : Data) :
    (offsetWord d).length ≤ (d.stacks 4).length+1 := by
  cases h9 : d.regs 9 <;> cases h8 : d.regs 8 <;> simp [offsetWord,h9,h8]

theorem coefficientOffset_eval (d : Data) (he : d.stacks 22=[])
    (ht : d.stacks 24=[]) :
    ∃ n rf, Eval coefficientOffset n d
      ⟨rf,Function.update d.stacks 22 (offsetWord d)⟩ ∧
      n ≤ 7*(d.stacks 4).length+9 ∧
      (∀ i : Fin 16, 2 ≤ i.val → rf i=d.regs i) := by
  cases h9 : d.regs 9 with
  | false =>
    cases h8 : d.regs 8 with
    | false =>
      have hs : (⟨d.regs,Function.update d.stacks 22 (offsetWord d)⟩ : Data)=d := by
        cases d with
        | mk regs stk =>
          simp_all [offsetWord]
      refine ⟨2,d.regs,?_,by omega,by intros; rfl⟩
      rw [hs]
      exact Eval.ite_false h9 (Eval.ite_false h8 (.base (.skip d)))
    | true =>
      have hc := copy_eval 4 22 d (by decide) (by decide) (by decide) ht
      have hs : copied 4 22 d=
          ⟨(copied 4 22 d).regs,Function.update d.stacks 22 (offsetWord d)⟩ := by
        simp [copied,StackRoutines.copyStacks,offsetWord,h8,h9,he]
      refine ⟨7*(d.stacks 4).length+7,(copied 4 22 d).regs,?_,by omega,?_⟩
      · rw [←hs]
        exact Eval.ite_false h9 (Eval.ite_true h8 hc)
      · exact copied_register 4 22 d
  | true =>
    have hc := copy_eval 4 22 d (by decide) (by decide) (by decide) ht
    have hp := push_eval 22 false (copied 4 22 d)
    let e := pushed 22 false (copied 4 22 d)
    have hs : e=⟨e.regs,Function.update d.stacks 22 (offsetWord d)⟩ := by
      simp [e,pushed,copied,StackRoutines.copyStacks,offsetWord,h9,he]
    refine ⟨7*(d.stacks 4).length+8,e.regs,?_,by omega,?_⟩
    · rw [←hs]
      exact Eval.ite_true h9 (hc.seq hp)
    · intro i hi
      exact (pushed_register 22 false (copied 4 22 d) i (by omega)).trans
        (copied_register 4 22 d i hi)

def coefficientValue (a b : Bool) (m : ℕ) : ℕ := if b then 2*m else if a then m else 0

theorem offsetWord_value_bits (d : Data) :
    BinaryArithmetic.toNat (offsetWord d)=coefficientValue (d.regs 8) (d.regs 9) (BinaryArithmetic.toNat (d.stacks 4)) := by
  cases h9 : d.regs 9 <;> cases h8 : d.regs 8 <;>
    simp [offsetWord,coefficientValue,h9,h8,toNat_cons,bitVal_false]

theorem coefficientValue_le (a b : Bool) (m : ℕ) : coefficientValue a b m ≤ 2*m := by
  cases b <;> cases a <;> simp [coefficientValue] ; omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
