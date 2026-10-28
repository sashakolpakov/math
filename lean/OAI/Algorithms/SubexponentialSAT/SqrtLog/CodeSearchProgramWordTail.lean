import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramScan

namespace OAI.Algorithms

/-! The actual decision tail for a proposed low-weight kernel word. It reads
both framed vectors, compares unary support with the runtime threshold, and
sets register 7 precisely on rejection. No semantic predicate is an opcode. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev wordTailCommand : Cmd 8 18 :=
  .seq (supportAt 8 9) <|
  .seq (.base (.atom (.peek 9 0 1))) <|
  .seq (.base (.atom (.bnot 6 1))) <|
  .seq (supportAt 12 10) <|
  .seq (.base (.atom (.peek 10 0 1))) <|
  .seq (.base (.atom (.band 7 6 1))) <|
  .seq (lessAt 10 16) (.base (.atom (.band 7 7 3)))

def wordTailProgram := compiled wordTailCommand 8 10

def wordTailBudget (outputSize inputSize : ℕ) := 10 * outputSize + 14 * inputSize + 18

private theorem replicate_present (w : ℕ) :
    (List.replicate w true).head?.isSome = decide (w ≠ 0) := by
  cases w <;> simp

private theorem cellWeight_le_length (xs : List (Bool × Bool)) :
    cellWeight xs ≤ xs.length := by
  induction xs with
  | nil => simp [cellWeight]
  | cons x xs ih =>
      simp only [cellWeight, List.length_cons]
      split <;> omega

theorem wordTail_eval (ys xs : List (Bool × Bool)) (d : ℕ) (base : ScanState)
    (hy : base.stacks 8 = framedCellStream ys)
    (hx : base.stacks 12 = framedCellStream xs)
    (h9 : base.stacks 9 = []) (h10 : base.stacks 10 = [])
    (hd : base.stacks 16 = List.replicate d true) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ wordTailBudget ys.length xs.length ∧
      Eval wordTailCommand n base next ∧
      next.regs 7 = decide (cellWeight ys = 0 ∧ cellWeight xs ≠ 0 ∧ cellWeight xs < d) ∧
      next.stacks 17 = base.stacks 17 := by
  obtain ⟨na, a, hna, hea, ha8, ha9, har, has⟩ :=
    supportAt_eval 8 9 (by decide) ys base hy h9
  let b := (Atom.peek 9 0 1).eval a
  let c := (Atom.bnot 6 1).eval b
  have hc6 : c.regs 6 = decide (cellWeight ys = 0) := by
    simp [c, b, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs, ha9,
      replicate_present]
  have hc12 : c.stacks 12 = framedCellStream xs := by
    change a.stacks 12 = _
    rw [has 12 (by decide) (by decide), hx]
  have hc10 : c.stacks 10 = [] := by
    change a.stacks 10 = _
    rw [has 10 (by decide) (by decide), h10]
  obtain ⟨nb, e, hnb, heb, he12, he10, her, hes⟩ :=
    supportAt_eval 12 10 (by decide) xs c hc12 hc10
  let f := (Atom.peek 10 0 1).eval e
  let g := (Atom.band 7 6 1).eval f
  have hg7 : g.regs 7 = decide (cellWeight ys = 0 ∧ cellWeight xs ≠ 0) := by
    have he6 := her 6 (by decide)
    rw [hc6] at he6
    simp [g, f, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs, he10,
      replicate_present, he6]
  have hg10 : g.stacks 10 = List.replicate (cellWeight xs) true := he10
  have hg16 : g.stacks 16 = List.replicate d true := by
    change e.stacks 16 = _
    rw [hes 16 (by decide) (by decide)]
    change a.stacks 16 = _
    rw [has 16 (by decide) (by decide), hd]
  obtain ⟨nc, h, hnc, hec, hh3, hhr, hhs⟩ := lessAt_eval 10 16 (by decide) g
  have hh7 := hhr 7 (by decide)
  rw [hg7] at hh7
  rw [hg10, hg16, List.length_replicate, List.length_replicate] at hh3
  let out := (Atom.band 7 7 3).eval h
  have hout : out.regs 7 =
      decide (cellWeight ys = 0 ∧ cellWeight xs ≠ 0 ∧ cellWeight xs < d) := by
    simp [out, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hh7, hh3, Bool.and_assoc]
  refine ⟨na + (1 + (1 + (nb + (1 + (1 + (nc + 1)))))), out, ?_, ?_, hout, ?_⟩
  · rw [hg10, List.length_replicate] at hnc
    have hw : cellWeight xs ≤ xs.length := cellWeight_le_length xs
    unfold wordTailBudget
    omega
  · exact hea.seq <| (Eval.base (.atom _ a)).seq <| (Eval.base (.atom _ b)).seq <|
      heb.seq <| (Eval.base (.atom _ e)).seq <| (Eval.base (.atom _ f)).seq <|
        hec.seq (Eval.base (.atom _ h))
  · change h.stacks 17 = _
    rw [hhs 17 (by decide) (by decide)]
    change e.stacks 17 = _
    rw [hes 17 (by decide) (by decide)]
    change a.stacks 17 = _
    exact has 17 (by decide) (by decide)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
