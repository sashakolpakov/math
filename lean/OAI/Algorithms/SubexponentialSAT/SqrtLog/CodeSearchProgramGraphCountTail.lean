import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramScan

namespace OAI.Algorithms

/-! Two physical support counters for a Walsh query. The parity count is kept
on tape9, while register7 reports whether the input character is nonzero. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev graphCountTail : Cmd 8 18 :=
  .seq (supportAt 8 9) <|
  .seq (supportAt 12 10) <|
  .seq (.base (.atom (.peek 10 0 1))) (.base (.atom (.copy 7 1)))

theorem graphCountTail_eval (ys xs : List (Bool × Bool)) (base : ScanState)
    (hy : base.stacks 8 = framedCellStream ys)
    (hx : base.stacks 12 = framedCellStream xs)
    (h9 : base.stacks 9 = []) (h10 : base.stacks 10 = []) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ 10 * ys.length + 10 * xs.length + 9 ∧
      Eval graphCountTail n base next ∧
      next.regs 7 = decide (cellWeight xs ≠ 0) ∧
      next.stacks 9 = List.replicate (cellWeight ys) true ∧
      next.stacks 16 = base.stacks 16 ∧ next.stacks 17 = base.stacks 17 := by
  obtain ⟨ny,y,hny,hey,hy8,hy9,hyr,hys⟩ := supportAt_eval 8 9 (by decide) ys base hy h9
  have hy12 : y.stacks 12 = framedCellStream xs := by
    rw [hys 12 (by decide) (by decide),hx]
  have hy10 : y.stacks 10 = [] := by rw [hys 10 (by decide) (by decide),h10]
  obtain ⟨nx,x,hnx,hex,hx12,hx10,hxr,hxs⟩ := supportAt_eval 12 10 (by decide) xs y hy12 hy10
  let peeked := (Atom.peek 10 0 1).eval x
  let out := (Atom.copy 7 1).eval peeked
  have hpresent : (List.replicate (cellWeight xs) true).head?.isSome =
      decide (cellWeight xs ≠ 0) := by cases cellWeight xs <;> simp
  refine ⟨ny+(nx+(1+1)),out,by omega,
    hey.seq (hex.seq ((Eval.base (.atom _ x)).seq (Eval.base (.atom _ peeked)))),?_,?_,?_,?_⟩
  · simp [out,peeked,Atom.eval,Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs,hx10,hpresent]
  · change x.stacks 9 = _
    rw [hxs 9 (by decide) (by decide),hy9]
  · change x.stacks 16 = _
    rw [hxs 16 (by decide) (by decide),hys 16 (by decide) (by decide)]
  · change x.stacks 17 = _
    rw [hxs 17 (by decide) (by decide),hys 17 (by decide) (by decide)]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
