import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramMatrix

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev startBlock : Cmd 2 18 := .seq (copy 14 15) (copy 1 12)
abbrev finishBlock : Cmd 2 18 := .seq (clear 15) (.base (.atom (.push 14 0)))
abbrev blockStep : Cmd 2 18 := .seq startBlock (.seq iScan finishBlock)

theorem startBlock_eval (s : Store) (regs : Fin 2 → Bool)
    (hi : s.ii = []) (hc : s.ic = []) :
    ∃ rf, Eval startBlock (7*s.ki.length + 7*s.degree.length + 10)
      (state regs s) (state rf {s with ii := s.ki, ic := s.degree}) := by
  let d := state regs s
  let a := afterCopy d 14 15
  have h1 := copy_eval d 14 15 (by decide) (by decide) (by decide) (by rfl)
  have h2 := copy_eval a 1 12 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 1 12 =
      state (afterCopy a 1 12).regs {s with ii := s.ki, ic := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterCopy, copyStacks, state, tapes, hi, hc]
  refine ⟨(afterCopy a 1 12).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  simp [a, d, afterCopy, copyStacks, state, tapes]
  omega

theorem finishBlock_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval finishBlock (2*s.ii.length+4) (state regs s)
      (state (readRegs regs 0 1 none) {s with ii := [], ki := false :: s.ki}) := by
  let a := afterClear (state regs s) 15
  have h1 := clear_eval (state regs s) 15
  have h2 : Eval (.base (.atom (.push 14 0))) 1 a
      (state (readRegs regs 0 1 none) {s with ii := [], ki := false :: s.ki}) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 2) (s := 18) 14 0) a
    apply Eval.base
    convert h using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, afterClear, clearStacks, state, tapes, StructuredProgram.Atom.instr, execInstr, readRegs]
  convert h1.seq h2 using 1 ; simp [state, tapes]

def blockBudget (B d C : ℕ) : ℕ := d*(rowBudget B d C+2) + 9*C + 7*d + 16

theorem blockStep_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hj : s.ji = []) (hcj : s.jc = []) (hi : s.ii = []) (hci : s.ic = [])
    (hcap : s.ki.length + 2*s.degree.length*s.degree.length ≤ C)
    (hv : ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ blockBudget s.width.length s.degree.length C, ∃ rf,
      Eval blockStep n (state regs s)
        (state rf {s with
          ki := false :: s.ki
          rev := (matrixBits rows s.degree.length s.ki.length s.degree.length).reverse ++ s.rev}) := by
  obtain ⟨r1, h1⟩ := startBlock_eval s regs hi hci
  let a : Store := {s with ii := s.ki, ic := s.degree}
  have hcap' : a.ii.length + a.ic.length*a.degree.length + a.degree.length*a.degree.length ≤ C := by
    dsimp [a]
    nlinarith
  obtain ⟨n, hn, r2, idx, hidx, h2⟩ := iScan_eval rows a r1 C hp hw hword hindex hj hcj hcap' hv
  let b : Store := {s with
    ic := []
    ii := idx
    rev := (matrixBits rows s.degree.length s.ki.length s.degree.length).reverse ++ s.rev}
  have h2' : Eval iScan n (state r1 a) (state r2 b) := h2
  have h3 := finishBlock_eval b r2
  refine ⟨(7*s.ki.length+7*s.degree.length+10)+(n+(2*idx.length+4)),
    ?_, readRegs r2 0 1 none, ?_⟩
  · dsimp [a] at hn hidx
    dsimp [blockBudget]
    nlinarith
  · simpa only [blockStep, a, b, hi, hci] using h1.seq (h2'.seq h3)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
