import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgramFetch
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- The extra cell changes the comparison from f < h to f ≤ h. -/
def bump (extra : Bool) : Code :=
  .seq (Subexp.TupleProgram.pushConst 9 0 true)
    (if extra then Subexp.TupleProgram.pushConst 9 0 true else .base .skip)

def bumped (d : Data) (extra : Bool) : Data :=
  ⟨Function.update d.regs 0 true,
    Function.update d.stacks 9 (unary (if extra then 2 else 1) ++ d.stacks 9)⟩

theorem bump_eval (d : Data) (extra : Bool) :
    Eval (bump extra) (if extra then 4 else 2) d (bumped d extra) := by
  have h := Subexp.TupleProgram.pushConst_eval (9 : Fin 16) (0 : Fin 8) true d
  cases extra with
  | false =>
    have he := h.seq (Eval.base (StructuredProgram.Eval.skip _))
    simpa [bump,bumped,Subexp.TupleProgram.pushedState] using he
  | true =>
    have he := h.seq (Subexp.TupleProgram.pushConst_eval (9 : Fin 16) (0 : Fin 8) true _)
    simpa [bump,bumped,Subexp.TupleProgram.pushedState,List.replicate_succ] using he

def test (extra : Bool) : Code := .seq (copy 6 8) (.seq (copy 3 9) (.seq (bump extra) lessClean))

theorem test_eval (d : Data) (f h : ℕ) (extra : Bool)
    (hf : d.stacks 6=Encoding.encodeNat f) (hh : d.stacks 3=unary h)
    (h8 : d.stacks 8=[]) (h9 : d.stacks 9=[]) (h14 : d.stacks 14=[]) :
    ∃ n e, n ≤ 13*f+9*h+45 ∧ Eval (test extra) n d e ∧
      e.regs 3=decide (f < h+(if extra then 1 else 0)) ∧ e.stacks=d.stacks ∧ Stable d e := by
  let a := afterCopy d 6 8 0 1
  let b := afterCopy a 3 9 0 1
  let c := bumped b extra
  have h1 : Eval (copy 6 8) (7*(f+1)+5) d a := by
    simpa [copy,hf] using copy_eval d 6 8 14 0 1 (by decide) (by decide) (by decide) (by decide) h14
  have h2 : Eval (copy 3 9) (7*h+5) a b := by
    simpa [copy,b,a,afterCopy,StackRoutines.copyStacks,hh] using
      copy_eval a 3 9 14 0 1 (by decide) (by decide) (by decide) (by decide)
        (by simpa [a,afterCopy,StackRoutines.copyStacks] using h14)
  have h3 := bump_eval b extra
  have hc8 : (c.stacks 8).length=f+1 := by
    simp [c,b,a,bumped,afterCopy,StackRoutines.copyStacks,hf,h8]
  have hc9 : (c.stacks 9).length=h+(if extra then 2 else 1) := by
    simp [c,b,a,bumped,afterCopy,StackRoutines.copyStacks,hh,h9,Nat.add_comm]
  obtain ⟨n,e,hn,he,hflag,hes,her⟩ := lessClean_eval c
  refine ⟨7*(f+1)+5+(7*h+5+((if extra then 4 else 2)+n)),e,?_,
    h1.seq (h2.seq (h3.seq he)),?_,?_,?_⟩
  · rw [hc8,hc9] at hn
    cases extra <;> simp_all <;> omega
  · rw [hc8,hc9] at hflag
    convert hflag using 2 ; cases extra <;> simp
  · rw [hes]
    funext i
    fin_cases i <;> simp [c,b,a,bumped,afterCopy,StackRoutines.copyStacks,h8,h9]
  · intro i hi
    rw [her i hi]
    have hi0 : i≠0 := by intro he; subst i; simp at hi
    have hi1 : i≠1 := by intro he; subst i; simp at hi
    simp [c,b,a,bumped,afterCopy,readRegs,hi0,hi1]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
