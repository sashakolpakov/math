import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramRows

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev startRow : Cmd 2 18 := .seq (copy 15 16) (copy 1 13)
abbrev finishRow : Cmd 2 18 := .seq (clear 16) (copy 1 15)
abbrev rowStep : Cmd 2 18 := .seq startRow (.seq jScan finishRow)

theorem startRow_eval (s : Store) (regs : Fin 2 → Bool)
    (hj : s.ji = []) (hc : s.jc = []) :
    ∃ rf, Eval startRow (7*s.ii.length + 7*s.degree.length + 10)
      (state regs s) (state rf {s with ji := s.ii, jc := s.degree}) := by
  let d := state regs s
  let a := afterCopy d 15 16
  have h1 := copy_eval d 15 16 (by decide) (by decide) (by decide) (by rfl)
  have h2 := copy_eval a 1 13 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 1 13 =
      state (afterCopy a 1 13).regs {s with ji := s.ii, jc := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterCopy, copyStacks, state, tapes, hj, hc]
  refine ⟨(afterCopy a 1 13).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  simp [a, d, afterCopy, copyStacks, state, tapes]
  omega

theorem finishRow_eval (s : Store) (regs : Fin 2 → Bool) :
    ∃ rf, Eval finishRow (2*s.ji.length + 7*s.degree.length + 8)
      (state regs s) (state rf {s with ji := [], ii := s.degree ++ s.ii}) := by
  let d := state regs s
  let a := afterClear d 16
  have h1 := clear_eval d 16
  have h2 := copy_eval a 1 15 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 1 15 =
      state (afterCopy a 1 15).regs {s with ji := [], ii := s.degree ++ s.ii} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterClear, copyStacks, clearStacks, state, tapes]
  refine ⟨(afterCopy a 1 15).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  simp [a, d, afterClear, clearStacks, state, tapes]
  omega

def rowBudget (B d C : ℕ) : ℕ := d * (emitBudget B d C + 2) + 9*C + 14*d + 20

theorem rowStep_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = []) (hj : s.ji = []) (hc : s.jc = [])
    (hcap : s.ii.length + s.degree.length*s.degree.length ≤ C)
    (hv : ∀ j < s.degree.length, s.ii.length+j*s.degree.length < rows.length) :
    ∃ n ≤ rowBudget s.width.length s.degree.length C, ∃ rf,
      Eval rowStep n (state regs s)
        (state rf {s with
          ii := s.degree ++ s.ii
          rev := (rowBits rows s.degree.length s.ii.length s.degree.length).reverse ++ s.rev}) := by
  obtain ⟨r1, h1⟩ := startRow_eval s regs hj hc
  let a : Store := {s with ji := s.ii, jc := s.degree}
  obtain ⟨n, hn, r2, idx, hidx, h2⟩ := jScan_eval rows a r1 C hp hw hword hindex hcap hv
  let b : Store := {s with
    jc := []
    ji := idx
    rev := (rowBits rows s.degree.length s.ii.length s.degree.length).reverse ++ s.rev}
  have h2' : Eval jScan n (state r1 a) (state r2 b) := h2
  obtain ⟨r3, h3⟩ := finishRow_eval b r2
  refine ⟨(7*s.ii.length + 7*s.degree.length + 10) +
    (n + (2*idx.length + 7*s.degree.length + 8)), ?_, r3, ?_⟩
  · dsimp [a] at hn hidx
    dsimp [rowBudget, b]
    nlinarith
  · simpa only [rowStep, a, b, hj, hc] using h1.seq (h2'.seq h3)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
