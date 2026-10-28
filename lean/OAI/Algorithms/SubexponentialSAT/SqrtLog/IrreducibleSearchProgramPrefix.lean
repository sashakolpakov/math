import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramDot

namespace OAI.Algorithms

/-! Runtime-length padded prefixes, with reversal by coefficient rather
than by bit. This is the physical stream preparation needed before a
convolution dot product. A unary count controls one fixed eight-label
program; exhaustion of the coefficient source supplies the zero cell. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

def paddedPrefix : ℕ → List IrreducibleSearch.F → List IrreducibleSearch.F
  | 0, _ => []
  | n + 1, as => as.headD 0 :: paddedPrefix n as.tail

@[simp] theorem paddedPrefix_length (n : ℕ) (as : List IrreducibleSearch.F) :
    (paddedPrefix n as).length = n := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih => simp [paddedPrefix, ih]

abbrev prefixReverseProgram : Program 6 3 8 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 1 4 5 1, .branch 5 2 7, .pop 0 0 2 3,
    .pop 0 1 2 4, .push 2 1 5, .push 2 0 6, .goto 0, .halt]

def prefixCfg (pc : Option (Fin 8)) (regs : Fin 6 → Bool)
    (source count output : List Bool) : Cfg 6 3 8 :=
  ⟨pc, regs, ![source, count, output]⟩

def prefixRoundRegs (regs : Fin 6 → Bool) (as : List IrreducibleSearch.F)
    (bit : Bool) : Fin 6 → Bool :=
  let r := readRegs regs 4 5 (some bit)
  let r := readRegs r 0 2 (coefficientArray as).head?
  readRegs r 1 2 (coefficientArray as).tail.head?

theorem prefix_round (regs : Fin 6 → Bool) (as : List IrreducibleSearch.F)
    (bit : Bool) (count output : List Bool) :
    Trace prefixReverseProgram 7
      (prefixCfg (some 0) regs (coefficientArray as) (bit :: count) output)
      (prefixCfg (some 0) (prefixRoundRegs regs as bit) (coefficientArray as.tail)
        count (coefficientWord (as.headD 0) ++ output)) := by
  have hz : scalarBits (0 : IrreducibleSearch.F) = (false, false) := by decide
  cases as with
  | nil =>
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, prefixReverseProgram, prefixCfg,
        prefixRoundRegs, execInstr, readRegs, coefficientWord_eq, hz,
        Function.update_apply]
      funext i
      fin_cases i <;> simp
  | cons a as =>
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, prefixReverseProgram, prefixCfg,
        prefixRoundRegs, execInstr, readRegs, coefficientWord_eq,
        Function.update_apply]
      funext i
      fin_cases i <;> simp

theorem prefix_exit (regs : Fin 6 → Bool) (source output : List Bool) :
    Trace prefixReverseProgram 3
      (prefixCfg (some 0) regs source [] output)
      (prefixCfg none (readRegs regs 4 5 none) source [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, prefixReverseProgram, prefixCfg,
    execInstr, readRegs, Function.update_apply]

theorem prefixReverse_trace (as : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 6 → Bool) :
    ∃ finalRegs, Trace prefixReverseProgram (7 * count.length + 3)
      (prefixCfg (some 0) regs (coefficientArray as) count output)
      (prefixCfg none finalRegs (coefficientArray (as.drop count.length)) []
        (coefficientArray (paddedPrefix count.length as).reverse ++ output)) := by
  induction count generalizing as regs output with
  | nil =>
      simpa [paddedPrefix] using Exists.intro (readRegs regs 4 5 none)
        (prefix_exit regs (coefficientArray as) output)
  | cons bit count ih =>
      obtain ⟨last, ht⟩ := ih as.tail (coefficientWord (as.headD 0) ++ output)
        (prefixRoundRegs regs as bit)
      refine ⟨last, ?_⟩
      have he := (prefix_round regs as bit count output).trans ht
      convert he using 1 <;>
        simp [paddedPrefix, List.reverse_cons, List.append_assoc,
          List.drop_tail] ; omega

theorem prefixReverse_primitive (as : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 6 → Bool) :
    ∃ finalRegs, Computation.RunsIn (primitive prefixReverseProgram).step
      (primitiveOverhead prefixReverseProgram * (7 * count.length + 3))
      (primitiveCfg prefixReverseProgram
        (prefixCfg (some 0) regs (coefficientArray as) count output))
      (primitiveCfg prefixReverseProgram
        (prefixCfg none finalRegs (coefficientArray (as.drop count.length)) []
          (coefficientArray (paddedPrefix count.length as).reverse ++ output))) := by
  obtain ⟨last, he⟩ := prefixReverse_trace as count output regs
  exact ⟨last, BitProgram.primitive_execution prefixReverseProgram ⟨_, Nat.le_refl _, he⟩⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
