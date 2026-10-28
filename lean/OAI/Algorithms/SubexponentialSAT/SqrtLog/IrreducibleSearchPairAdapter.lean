import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramLift
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! A fixed physical split of a concatenated pair of coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

open BitProgram StructuredCalls SubexpSetupStorage IrreducibleSearchProgram

private theorem paddedPrefix_append_left (as bs : List IrreducibleSearch.F) :
    paddedPrefix as.length (as ++ bs) = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [paddedPrefix] using congrArg (List.cons a) ih

def registers : Fin 6 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩,
    by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) h⟩
def firstPorts : Fin 3 ↪ Fin 6 := ⟨![0, 2, 3], by decide⟩
def secondPorts : Fin 3 ↪ Fin 6 := ⟨![3, 2, 4], by decide⟩

abbrev command : Cmd 16 6 :=
  .seq (copyCmd 1 2 5) (.seq (prefixCall registers firstPorts)
    (.seq (copyCmd 1 2 5) (prefixCall registers secondPorts)))
def program := compiled command 0 4

def input (as bs : List IrreducibleSearch.F) (count : List Bool)
    (regs : Fin 16 → Bool) : State 16 6 :=
  ⟨regs, ![coefficientArray (as ++ bs), count, [], [], [], []]⟩
def output (as bs : List IrreducibleSearch.F) (count : List Bool)
    (regs : Fin 16 → Bool) : State 16 6 :=
  ⟨regs, ![coefficientArray bs, count, [], [], coefficientArray as, []]⟩

theorem command_eval (as bs : List IrreducibleSearch.F) (count : List Bool)
    (hc : count.length = as.length) (regs : Fin 16 → Bool) :
    ∃ finalRegs, Eval command (28 * count.length + 16)
      (input as bs count regs) (output as bs count finalRegs) := by
  let a := input as bs count regs
  let b := copyState (1 : Fin 6) 2 a
  have e1 := copy_eval (1 : Fin 6) 2 5 a (by decide) (by decide) (by decide)
    (by simp [a, input])
  obtain ⟨r2, e2⟩ := prefixCall_eval registers firstPorts (as ++ bs) count [] b
    (by simp [b, a, copyState, StackRoutines.copyStacks, input, firstPorts])
    (by simp [b, a, copyState, StackRoutines.copyStacks, input, firstPorts])
    (by simp [b, a, copyState, StackRoutines.copyStacks, input, firstPorts])
  simp only [hc, List.drop_left, paddedPrefix_append_left, List.append_nil] at e2
  let c := afterThree registers firstPorts r2 (coefficientArray bs) []
    (coefficientArray as.reverse) b
  change Eval _ _ _ c at e2
  let d := copyState (1 : Fin 6) 2 c
  have e3 := copy_eval (1 : Fin 6) 2 5 c (by decide) (by decide) (by decide)
    (by simp [c, b, a, afterThree, replaceThree, firstPorts,
      copyState, StackRoutines.copyStacks, input])
  obtain ⟨r4, e4⟩ := prefixCall_eval registers secondPorts as.reverse count [] d
    (by simp [d, c, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, firstPorts, secondPorts])
    (by simp [d, c, b, a, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, firstPorts, secondPorts, input])
    (by simp [d, c, b, a, copyState, StackRoutines.copyStacks, afterThree,
      replaceThree, firstPorts, secondPorts, input])
  have hdrop : as.reverse.drop count.length = [] := by
    apply List.drop_eq_nil_iff.mpr
    simp [hc]
  have hpad : paddedPrefix count.length as.reverse = as.reverse :=
    paddedPrefix_of_length _ _ (by simp [hc])
  simp only [hdrop, hpad, List.reverse_reverse, coefficientArray_nil,
    List.append_nil] at e4
  let e := afterThree registers secondPorts r4 [] [] (coefficientArray as) d
  change Eval _ _ _ e at e4
  have he := e1.seq (e2.seq (e3.seq e4))
  have hend : e = output as bs count e.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext i
    fin_cases i <;> simp [e, d, c, b, a, afterThree, replaceThree,
      firstPorts, secondPorts, copyState, StackRoutines.copyStacks, input, output]
  rw [hend] at he
  refine ⟨e.regs, ?_⟩
  convert he using 1 ;
    simp [a, c, b, input, afterThree, replaceThree, firstPorts,
      copyState, StackRoutines.copyStacks, hc] ; omega

theorem program_runsIn (as bs : List IrreducibleSearch.F) (count : List Bool)
    (hc : count.length = as.length) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn program (28 * count.length + 17)
      ((input as bs count regs).withPC (some program.entry))
      ((output as bs count finalRegs).withPC none) := by
  obtain ⟨rf, he⟩ := command_eval as bs count hc regs
  exact ⟨rf, _, by omega, compiled_halt_trace he 0 4⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

end OAI.Algorithms
