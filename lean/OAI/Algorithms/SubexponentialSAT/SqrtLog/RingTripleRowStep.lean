import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleRows

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev startRow : Cmd 2 16 := .seq (load 2) (.seq (copy 1 5) (copy 9 12))

theorem startRow_eval (B : ℕ) (s : Store) (regs : Fin 2 → Bool)
    (x xt : List Bool) (hx : x.length = B) (hw : s.width.length = B) :
    ∃ regs', Eval startRow (14 * B + 7 * s.y.length + 7 * s.degree.length + 22)
      (state regs {s with xs := x ++ xt, held := [], ys := [], jc := []})
      (state regs' {s with xs := xt, held := x, ys := s.y, jc := s.degree}) := by
  let d := state regs {s with xs := x ++ xt, held := [], ys := [], jc := []}
  let a := afterLoad d 2 x xt
  let b := afterCopy a 1 5
  have h1 := load_eval d 2 x xt (by rfl) (by rfl) (by rfl)
    (by simpa [d, state, tapes] using (hw.trans hx.symm))
  have h2 := copy_eval a 1 5 (by decide) (by decide) (by decide) (by rfl)
  have h3 := copy_eval b 9 12 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy b 9 12 =
      state (afterCopy b 9 12).regs {s with xs := xt, held := x, ys := s.y, jc := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [b, a, d, afterCopy, afterLoad, copyStacks, loadPorts, state, tapes]
  refine ⟨(afterCopy b 9 12).regs, ?_⟩
  rw [← hf]
  convert h1.seq (h2.seq h3) using 1
  simp [b, a, d, afterCopy, afterLoad, copyStacks, loadPorts, state, tapes, hx]
  omega

theorem clearHeld_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (clear 6) (2 * s.held.length + 3) (state regs s)
      (state (readRegs regs 0 1 none) {s with held := []}) := by
  have he := clear_eval (state regs s) 6
  convert he using 1
  · simp [state, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [state, tapes, clearStacks]

abbrev rowStep : Cmd 2 16 := .seq startRow (.seq jScan (clear 6))

theorem rowStep_eval (B : ℕ) (s : Store) (regs : Fin 2 → Bool)
    (x : Word B) (pairs : List (Word B × Word B)) (xt ct : List Bool)
    (hy : leftBits pairs = s.y) (hd : s.degree.length = pairs.length)
    (hw : s.width.length = B) :
    ∃ n ≤ 100 * (s.degree.length + 1) * (B + 1), ∃ regs',
      Eval rowStep n
        (state regs {s with xs := x.val ++ xt, table := rightBits pairs ++ ct, held := [], ys := [], jc := []})
        (state regs' {s with xs := xt, table := ct, held := [], ys := [], jc := [], out := (rowBits x.val pairs).reverse ++ s.out}) := by
  obtain ⟨r₁, hstart⟩ := startRow_eval B {s with table := rightBits pairs ++ ct}
    regs x.val xt x.property hw
  let a := {s with xs := xt, held := x.val}
  obtain ⟨n, hn, r₂, hscan⟩ := jScan_eval B a pairs ct s.degree r₁ hd x.property hw
  have hscan' : Eval jScan n
      (state r₁ {s with table := rightBits pairs ++ ct, xs := xt, held := x.val, ys := s.y, jc := s.degree})
      (state r₂ {s with xs := xt, table := ct, held := x.val, ys := [], jc := [], out := (rowBits x.val pairs).reverse ++ s.out}) := by
    simpa [a, hy] using hscan
  have hclear := clearHeld_eval
    {s with xs := xt, table := ct, held := x.val, ys := [], jc := [], out := (rowBits x.val pairs).reverse ++ s.out} r₂
  refine ⟨(14 * B + 7 * s.y.length + 7 * s.degree.length + 22) + (n + (2 * B + 3)),
    ?_, readRegs r₂ 0 1 none, ?_⟩
  · have hyl : s.y.length = pairs.length * B := by rw [← hy, leftBits_length]
    rw [← hd] at hyl hn
    nlinarith
  · simpa only [x.property] using hstart.seq (hscan'.seq hclear)

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
