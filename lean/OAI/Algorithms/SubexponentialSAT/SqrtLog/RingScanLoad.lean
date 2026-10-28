import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# A fixed-control dynamic coefficient loader

The source contains a flat vector. A preserved unary width word determines
how many bits are removed. Exactly that many bits are prefixed, in their
original order, to the destination. Control size is independent of both the
width and the number of coefficients.
-/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines ArrayPrograms

def loadTapes (src dst width count scratch : List Bool) : Fin 5 → List Bool :=
  ![src, dst, width, count, scratch]

def loadState (regs : Fin 2 → Bool) (src dst width count scratch : List Bool) : State 2 5 :=
  ⟨regs, loadTapes src dst width count scratch⟩

abbrev loadWord : Cmd 2 5 :=
  .seq (.call (copyProgram 2 3 4 0 1))
    (.seq (.call (countedTransferProgram 3 0 4 0 1))
      (.call (transferProgram 4 1 0 1)))

private theorem load_copy_stacks (src dst width : List Bool) :
    copyStacks (2 : Fin 5) 3 (loadTapes src dst width [] []) =
      loadTapes src dst width width [] := by
  funext i
  fin_cases i <;> simp [copyStacks, loadTapes]

private theorem load_counted_stacks (word tail dst width : List Bool) :
    countedTransferStacks (3 : Fin 5) 0 4 word tail
      (loadTapes (word ++ tail) dst width width []) =
      loadTapes tail dst width [] word.reverse := by
  funext i
  fin_cases i <;> simp [countedTransferStacks, loadTapes]

private theorem load_finish_stacks (word tail dst width : List Bool) :
    transferStacks (4 : Fin 5) 1 (loadTapes tail dst width [] word.reverse) =
      loadTapes tail (word ++ dst) width [] [] := by
  funext i
  fin_cases i <;> simp [transferStacks, loadTapes]

/-- A genuine fixed-program execution. The width is input data and is restored.
The exact cost includes the halt/return of each of the three subroutines. -/
theorem loadWord_eval (regs : Fin 2 → Bool) (word tail dst width : List Bool)
    (hwidth : width.length = word.length) :
    Eval loadWord (14 * word.length + 11)
      (loadState regs (word ++ tail) dst width [] [])
      (loadState (readRegs regs 0 1 none) tail (word ++ dst) width [] []) := by
  let rr := readRegs regs (0 : Fin 2) 1 none
  have hcopy := copyProgram_trace (2 : Fin 5) 3 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    regs (loadTapes (word ++ tail) dst width [] []) (by rfl)
  have hcopy' := halt_after_trace _ hcopy 7 rfl rfl
  have ecopy : Eval (.call (copyProgram (2 : Fin 5) 3 4 (0 : Fin 2) 1))
      (7 * width.length + 5)
      (loadState regs (word ++ tail) dst width [] [])
      (loadState rr (word ++ tail) dst width width []) := by
    apply Eval.call
    simpa only [loadState, StructuredProgram.State.withPC, copyResult, load_copy_stacks, rr,
      show loadTapes (word ++ tail) dst width [] [] 2 = width from rfl, Nat.add_assoc] using hcopy'
  have htake := countedTransferProgram_trace (3 : Fin 5) 0 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    word tail width rr (loadTapes (word ++ tail) dst width width [])
    rfl rfl hwidth
  have htake' := halt_after_trace _ htake 4 rfl rfl
  have etake : Eval (.call (countedTransferProgram (3 : Fin 5) 0 4 (0 : Fin 2) 1))
      (4 * word.length + 3)
      (loadState rr (word ++ tail) dst width width [])
      (loadState rr tail dst width [] word.reverse) := by
    apply Eval.call
    simpa [loadState, StructuredProgram.State.withPC, countedTransferProgram,
      countedTransferResult, load_counted_stacks, rr, readRegs_reset, Nat.add_assoc] using htake'
  have hfinish := transferProgram_trace (4 : Fin 5) 1 (0 : Fin 2) 1
    (by decide) (by decide) rr (loadTapes tail dst width [] word.reverse)
  have hfinish' := halt_after_trace _ hfinish 3 rfl rfl
  have efinish : Eval (.call (transferProgram (4 : Fin 5) 1 (0 : Fin 2) 1))
      (3 * word.length + 3)
      (loadState rr tail dst width [] word.reverse)
      (loadState rr tail (word ++ dst) width [] []) := by
    apply Eval.call
    simpa only [loadState, StructuredProgram.State.withPC, transferResult, load_finish_stacks,
      show loadTapes tail dst width [] word.reverse 4 = word.reverse from rfl, List.length_reverse, rr, readRegs_reset,
      Nat.add_assoc] using hfinish'
  have he := ecopy.seq (etake.seq efinish)
  convert he using 1 ; simp only [hwidth] ; omega

abbrev loadWordProgram : Program 2 5 (size loadWord + 1) := compiled loadWord 0 1

theorem loadWordProgram_size : size loadWord + 1 = 18 := rfl

theorem loadWordProgram_trace (regs : Fin 2 → Bool) (word tail dst width : List Bool)
    (hwidth : width.length = word.length) :
    Trace loadWordProgram (14 * word.length + 12)
      ((loadState regs (word ++ tail) dst width [] []).withPC (some loadWordProgram.entry))
      ((loadState (readRegs regs 0 1 none) tail (word ++ dst) width [] []).withPC none) := by
  simpa only [Nat.add_assoc] using compiled_halt_trace (loadWord_eval regs word tail dst width hwidth) 0 1

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
