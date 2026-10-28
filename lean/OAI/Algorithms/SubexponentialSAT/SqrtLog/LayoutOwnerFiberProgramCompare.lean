import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramCore

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def compareSlots : Fin 7 → Fin 11 := ![0,1,2,3,5,6,7]
theorem compareSlots_injective : Function.Injective compareSlots := by decide

def compare : Code := liftCommand SubexponentialSAT.SubexpNodeIndexProgram.Internal.compare 3 4 id compareSlots

theorem compare_eval (regs : Fin 5 → Bool)
    (q m s left decoded right tmp i a c o : List Bool) :
    ∃ n ≤ 9*(left.length+1)+1, ∃ rr left' right',
      Eval compare n (data regs q m s left decoded right tmp i a c o)
        (data rr q m s left' decoded right' tmp i a c o) ∧
      rr 4=decide (left=right) ∧ left'.length ≤ left.length ∧ right'.length ≤ right.length := by
  obtain ⟨n,hn,rr,l,r,he,hf,hl,hr⟩ :=
    SubexponentialSAT.SubexpNodeIndexProgram.Internal.compare_eval regs q m s left right tmp i
  let d := data regs q m s left decoded right tmp i a c o
  have hin : projectState id compareSlots d=
      SubexponentialSAT.SubexpNodeIndexProgram.Internal.state regs q m s left right tmp i := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> rfl
  rw [← hin] at he
  have h := eval_liftCommand_from_state SubexponentialSAT.SubexpNodeIndexProgram.Internal.compare
    3 4 id compareSlots d Function.injective_id compareSlots_injective he
  have hout : embedState id compareSlots d
      (SubexponentialSAT.SubexpNodeIndexProgram.Internal.state rr q m s l r tmp i)=
        data rr q m s l decoded r tmp i a c o := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id compareSlots_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j <;> simp_all [d,data,compareSlots,Fin.exists_fin_succ]
  rw [hout] at h
  exact ⟨n+1,by omega,rr,l,r,h,hf,hl,hr⟩

def copyQuery : Code := .call (StackRoutines.copyProgram 0 5 6 0 1)

theorem copyQuery_eval (regs : Fin 5 → Bool)
    (q m s owner i a c o : List Bool) :
    Eval copyQuery (7*q.length+5)
      (data regs q m s owner [] [] [] i a c o)
      (data (status regs false false) q m s owner [] q [] i a c o) := by
  have h := copy_eval (data regs q m s owner [] [] [] i a c o)
    0 5 6 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  convert h using 1
  · rfl
  · simp [data]
  · apply state_ext
    · simp [afterCopy,data]
    · funext j; fin_cases j <;> simp [afterCopy,data,StackRoutines.copyStacks]

def compareOwner : Code := .seq copyQuery (.seq compare (.seq (clear 3) (clear 5)))

/-- Both originals are preserved; consumed equality operands and residuals
are cleared with their actual lengths charged. -/
theorem compareOwner_eval (regs : Fin 5 → Bool)
    (q m s owner i a c o : List Bool) :
    ∃ n ≤ 11*owner.length+9*q.length+21, ∃ rr,
      Eval compareOwner n (data regs q m s owner [] [] [] i a c o)
        (data rr q m s [] [] [] [] i a c o) ∧ rr 4=decide (owner=q) := by
  have h1 := copyQuery_eval regs q m s owner i a c o
  obtain ⟨n,hn,rr,l,r,h2,hf,hl,hr⟩ :=
    compare_eval (status regs false false) q m s owner [] q [] i a c o
  have h3 := clear_eval 3 (data rr q m s l [] r [] i a c o)
  have he3 : cleared (data rr q m s l [] r [] i a c o) 3=
      data (status rr false false) q m s [] [] r [] i a c o := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> simp [cleared,data]
  rw [he3] at h3
  have h4 := clear_eval 5 (data (status rr false false) q m s [] [] r [] i a c o)
  have he4 : cleared (data (status rr false false) q m s [] [] r [] i a c o) 5=
      data (status rr false false) q m s [] [] [] [] i a c o := by
    apply state_ext
    · simp [cleared,data]
    · funext j; fin_cases j <;> simp [cleared,data]
  rw [he4] at h4
  refine ⟨(7*q.length+5)+(n+((2*l.length+3)+(2*r.length+3))),by omega,
    status rr false false,?_,?_⟩
  · exact h1.seq (h2.seq (h3.seq h4))
  · simpa [status] using hf

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
