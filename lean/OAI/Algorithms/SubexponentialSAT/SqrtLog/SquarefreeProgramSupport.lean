import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeMask
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! Fixed primitive bit-mask union. Both runtime input words have the same
length. The output is prepended in reverse order; no list operation is atomic
and the instruction table does not depend on the word length. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev MaskData := State 5 3

def maskData (regs : Fin 5 → Bool) (left right output : List Bool) : MaskData :=
  ⟨regs, ![left, right, output]⟩

abbrev maskBody : Cmd 5 3 :=
  .seq (.atom (.pop 0 0 2))
    (.seq (.atom (.pop 1 1 3))
      (.seq (.atom (.bor 4 0 1))
        (.seq (.atom (.push 2 4)) (.atom (.peek 0 0 2)))))

abbrev maskLoop : Cmd 5 3 := .while 2 maskBody

abbrev maskUnion : Cmd 5 3 := .seq (.atom (.peek 0 0 2)) maskLoop

def maskReady (regs : Fin 5 → Bool) (left right output : List Bool) : MaskData :=
  maskData (readRegs regs 0 2 left.head?) left right output

theorem maskBody_eval (regs : Fin 5 → Bool) (a b : Bool)
    (left right output : List Bool) :
    ∃ regs', Eval maskBody 5 (maskData regs (a :: left) (b :: right) output)
      (maskReady regs' left right ((a || b) :: output)) := by
  let d := maskData regs (a :: left) (b :: right) output
  let d1 := (Atom.pop (0 : Fin 3) (0 : Fin 5) 2).eval d
  let d2 := (Atom.pop (1 : Fin 3) (1 : Fin 5) 3).eval d1
  let d3 := (Atom.bor (4 : Fin 5) 0 1).eval d2
  let d4 := (Atom.push (2 : Fin 3) (4 : Fin 5)).eval d3
  refine ⟨d3.regs, ?_⟩
  have he := Eval.seq (Eval.atom (Atom.pop (0 : Fin 3) (0 : Fin 5) 2) d)
    (Eval.seq (Eval.atom (Atom.pop (1 : Fin 3) (1 : Fin 5) 3) d1)
      (Eval.seq (Eval.atom (Atom.bor (4 : Fin 5) 0 1) d2)
        (Eval.seq (Eval.atom (Atom.push (2 : Fin 3) (4 : Fin 5)) d3)
          (Eval.atom (Atom.peek (0 : Fin 3) (0 : Fin 5) 2) d4))))
  convert he using 1 ;
    simp [ maskReady, maskData, d, d1, d2, d3, d4, Atom.eval,
      Atom.instr, State.ofCfg, execInstr, readRegs, Function.update] ;
    try (funext i; fin_cases i <;> rfl)

@[simp] theorem maskReady_guard (regs : Fin 5 → Bool) (left right output : List Bool) :
    (maskReady regs left right output).regs 2 = !left.isEmpty := by
  cases left <;> simp [maskReady, maskData, readRegs]

theorem maskLoop_eval (left right output : List Bool) (regs : Fin 5 → Bool)
    (hlen : left.length = right.length) :
    ∃ regs', Eval maskLoop (6 * left.length + 1) (maskReady regs left right output)
      (maskData regs' [] [] ((List.zipWith (· || ·) left right).reverse ++ output)) := by
  induction left generalizing right output regs with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp hlen.symm
    subst right
    refine ⟨(maskReady regs [] [] output).regs, ?_⟩
    simpa [maskLoop, maskReady, maskData] using
      (Eval.while_false (body := maskBody) (maskReady_guard regs [] [] output))
  | cons a left ih =>
    cases right with
    | nil => simp at hlen
    | cons b right =>
      have ht : left.length = right.length := by simpa using hlen
      obtain ⟨middle, hb⟩ := maskBody_eval (maskReady regs (a :: left) (b :: right) output).regs
        a b left right output
      obtain ⟨final, hf⟩ := ih right ((a || b) :: output) middle ht
      refine ⟨final, ?_⟩
      have hh := Eval.while_true (by simp : (maskReady regs (a :: left) (b :: right) output).regs 2 = true) hb hf
      have hc : 5 + (6 * left.length + 1) + 1 = 6 * (a :: left).length + 1 := by
        simp only [List.length_cons]; omega
      rw [hc] at hh
      simpa [maskLoop, maskReady, maskData, List.zipWith_cons_cons, List.reverse_cons,
        List.append_assoc] using hh

theorem maskUnion_eval (left right output : List Bool) (regs : Fin 5 → Bool)
    (hlen : left.length = right.length) :
    ∃ regs', Eval maskUnion (6 * left.length + 2) (maskData regs left right output)
      (maskData regs' [] [] ((List.zipWith (· || ·) left right).reverse ++ output)) := by
  obtain ⟨final, hf⟩ := maskLoop_eval left right output regs hlen
  refine ⟨final, ?_⟩
  have hp : Eval (.atom (.peek 0 0 2)) 1 (maskData regs left right output)
      (maskReady regs left right output) := Eval.atom _ _
  have hc : 1 + (6 * left.length + 1) = 6 * left.length + 2 := by omega
  have he := hp.seq hf
  rw [hc] at he
  exact he

def maskUnionProgram := compiled maskUnion 0 2

@[simp] theorem maskUnion_control_size : size maskUnion = 7 := rfl

theorem maskUnion_trace (left right output : List Bool) (regs : Fin 5 → Bool)
    (hlen : left.length = right.length) :
    ∃ regs', Trace maskUnionProgram (6 * left.length + 3)
      ((maskData regs left right output).withPC (some maskUnionProgram.entry))
      ((maskData regs' [] [] ((List.zipWith (· || ·) left right).reverse ++ output)).withPC none) := by
  obtain ⟨final, hf⟩ := maskUnion_eval left right output regs hlen
  exact ⟨final, by simpa [maskUnionProgram, Nat.add_assoc] using compiled_halt_trace hf 0 2⟩

/-- Semantic bridge: the exact bit program computes finite-set support union. -/
theorem supportUnion_trace {n : ℕ} (left right : Finset (Fin n))
    (output : List Bool) (regs : Fin 5 → Bool) :
    ∃ final, Trace maskUnionProgram (6 * n + 3)
      ((maskData regs (encodeMask left) (encodeMask right) output).withPC
        (some maskUnionProgram.entry))
      ((maskData final [] [] ((encodeMask (left ∪ right)).reverse ++ output)).withPC none) := by
  simpa only [encodeMask_length, encodeMask_union] using
    maskUnion_trace (encodeMask left) (encodeMask right) output regs
      (by simp only [encodeMask_length])

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
