import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! A fixed native loop produces a unary square from a unary input. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines

def countTapes (source counter out : List Bool) : Fin 4 → List Bool := ![source, counter, out, []]
abbrev countState (regs : Fin 2 → Bool) (source counter out : List Bool) : State 2 4 :=
  ⟨regs, countTapes source counter out⟩

abbrev countCopy : Cmd 2 4 := .call (copyProgram 0 2 3 0 1)
abbrev countInit : Cmd 2 4 := .call (copyProgram 0 1 3 0 1)
abbrev countPop : Cmd 2 4 := .base (.atom (.pop 1 0 1))
abbrev countLoop : Cmd 2 4 := .while 1 (.seq countCopy countPop)
abbrev countScan : Cmd 2 4 := .seq countPop countLoop
abbrev countSquare : Cmd 2 4 := .seq countInit countScan

def repeatCount (source : List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => source ++ repeatCount source n

@[simp] theorem repeatCount_length (source : List Bool) (n : ℕ) :
    (repeatCount source n).length = n*source.length := by
  induction n with
  | zero => simp [repeatCount]
  | succ n ih => simp [repeatCount, ih, Nat.add_mul, Nat.add_comm]

private theorem count_copy_stacks (source counter out : List Bool) :
    copyStacks (0 : Fin 4) 2 (countTapes source counter out) =
      countTapes source counter (source ++ out) := by
  funext i; fin_cases i <;> simp [copyStacks, countTapes]

private theorem count_init_stacks (source out : List Bool) :
    copyStacks (0 : Fin 4) 1 (countTapes source [] out) = countTapes source source out := by
  funext i; fin_cases i <;> simp [copyStacks, countTapes]

theorem countCopy_eval (regs : Fin 2 → Bool) (source counter out : List Bool) :
    Eval countCopy (7*source.length+5) (countState regs source counter out)
      (countState (readRegs regs 0 1 none) source counter (source ++ out)) := by
  apply Eval.call
  simpa only [countState, StructuredProgram.State.withPC, copyResult, count_copy_stacks,
    show countTapes source counter out 0 = source from rfl, Nat.add_assoc] using
    ListRegisterProgram.copy_run (0 : Fin 4) 2 3 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) regs (countTapes source counter out) (by rfl)

theorem countInit_eval (regs : Fin 2 → Bool) (source out : List Bool) :
    Eval countInit (7*source.length+5) (countState regs source [] out)
      (countState (readRegs regs 0 1 none) source source out) := by
  apply Eval.call
  simpa only [countState, StructuredProgram.State.withPC, copyResult, count_init_stacks,
    show countTapes source [] out 0 = source from rfl, Nat.add_assoc] using
    ListRegisterProgram.copy_run (0 : Fin 4) 1 3 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) regs (countTapes source [] out) (by rfl)

theorem countPop_eval (regs : Fin 2 → Bool) (source counter out : List Bool) :
    Eval countPop 1 (countState regs source counter out)
      (countState (readRegs regs 0 1 counter.head?) source counter.tail out) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 4) 1 0 1)
    (countState regs source counter out) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> cases counter <;>
      simp [ StructuredProgram.Atom.instr, execInstr, countTapes]

private theorem repeatCount_append (source : List Bool) (n : ℕ) :
    repeatCount source n ++ source = source ++ repeatCount source n := by
  induction n with
  | zero => simp [repeatCount]
  | succ n ih => simp only [repeatCount, List.append_assoc, ih]

private theorem countLoop_eval (regs : Fin 2 → Bool) (source counter out : List Bool) :
    ∃ rf, Eval countLoop (counter.length*(7*source.length+7)+1)
      (countState (readRegs regs 0 1 counter.head?) source counter.tail out)
      (countState rf source [] (repeatCount source counter.length ++ out)) := by
  induction counter generalizing regs out with
  | nil =>
      refine ⟨readRegs regs 0 1 none, ?_⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, List.head?_nil, List.tail_nil, repeatCount, List.nil_append]
      apply Eval.while_false
      simp [ readRegs_present]
  | cons bit counter ih =>
      have hc := countCopy_eval (readRegs regs 0 1 (some bit)) source counter out
      have hp := countPop_eval (readRegs (readRegs regs 0 1 (some bit)) 0 1 none) source counter (source ++ out)
      obtain ⟨rf, hl⟩ := ih (readRegs (readRegs regs 0 1 (some bit)) 0 1 none) (source ++ out)
      have he := Eval.while_true
        (show (countState (readRegs regs 0 1 (some bit)) source counter out).regs 1 = true by
          simp [ readRegs_present]) (hc.seq hp) hl
      refine ⟨rf, ?_⟩
      convert he using 1 <;>
        simp [List.length_cons, repeatCount, List.append_assoc ] <;>
        try ring
      apply congrArg (countTapes source [])
      exact (List.append_assoc source (repeatCount source counter.length) out).symm.trans
        ((congrArg (fun l => l ++ out)
          (repeatCount_append source counter.length).symm).trans
          (List.append_assoc _ _ _))

theorem countSquare_eval (regs : Fin 2 → Bool) (source : List Bool) :
    ∃ rf, Eval countSquare (7*source.length^2+14*source.length+7)
      (countState regs source [] [])
      (countState rf source [] (repeatCount source source.length)) := by
  have hi := countInit_eval regs source []
  have hp := countPop_eval (readRegs regs 0 1 none) source source []
  obtain ⟨rf, hl⟩ := countLoop_eval (readRegs regs 0 1 none) source source []
  refine ⟨rf, ?_⟩
  have he := hi.seq (hp.seq hl)
  simp only [List.append_nil] at he
  convert he using 1 ; ring

abbrev countSquareProgram : Program 2 4 (size countSquare+1) := compiled countSquare 0 2

theorem countSquareProgram_trace (regs : Fin 2 → Bool) (source : List Bool) :
    ∃ rf, Trace countSquareProgram (7*source.length^2+14*source.length+8)
      ((countState regs source [] []).withPC (some countSquareProgram.entry))
      ((countState rf source [] (repeatCount source source.length)).withPC none) := by
  obtain ⟨rf, he⟩ := countSquare_eval regs source
  exact ⟨rf, by simpa only [Nat.add_assoc] using compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
