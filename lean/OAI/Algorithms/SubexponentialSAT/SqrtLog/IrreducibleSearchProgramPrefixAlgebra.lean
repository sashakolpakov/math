import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramPrefix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramDotRun

namespace OAI.Algorithms

/-! Exact relationship between the paid prefix generator and the streams
used in the complete scalar convolution test. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem paddedPrefix_getElem? (n : ℕ) (as : List IrreducibleSearch.F) (i : ℕ) :
    (paddedPrefix n as)[i]? =
      if i < n then some (as[i]?.getD 0) else none := by
  induction n generalizing as i with
  | zero => simp [paddedPrefix]
  | succ n ih =>
      cases i with
      | zero => cases as <;> simp [paddedPrefix]
      | succ i => simp [paddedPrefix, ih]

theorem paddedPrefix_ofFn {d : ℕ} (a : Fin d → IrreducibleSearch.F) (n : ℕ) :
    paddedPrefix n (List.ofFn a) =
      List.ofFn (fun i : Fin n => IrreducibleSearch.entry a i) := by
  apply List.ext_getElem?
  intro i
  rw [paddedPrefix_getElem?]
  by_cases hn : i < n
  · by_cases hd : i < d
    · simp [ hn, hd, IrreducibleSearch.entry]
    · simp [ hn, hd, IrreducibleSearch.entry]
  · simp [ hn]

theorem paddedPrefix_self (as : List IrreducibleSearch.F) :
    paddedPrefix as.length as = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [paddedPrefix] using congrArg (List.cons a) ih

theorem paddedPrefix_of_length (as : List IrreducibleSearch.F) (n : ℕ)
    (h : as.length = n) : paddedPrefix n as = as := by
  rw [← h, paddedPrefix_self]

theorem paddedPrefix_convolutionLeft {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :
    paddedPrefix (j + 1) (List.ofFn a) = convolutionLeft a j :=
  paddedPrefix_ofFn a (j + 1)

theorem reverse_convolutionLeft {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :
    (convolutionLeft a j).reverse = convolutionRight a j := by
  unfold convolutionLeft convolutionRight
  apply List.ext_getElem (by simp only [List.length_reverse, List.length_ofFn])
  intro i hi hi'
  rw [List.getElem_reverse]
  simp only [List.length_ofFn, List.getElem_ofFn]
  congr 1

theorem paddedPrefix_convolutionRight {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :
    (paddedPrefix (j + 1) (List.ofFn a)).reverse = convolutionRight a j := by
  rw [paddedPrefix_convolutionLeft, reverse_convolutionLeft]

theorem prefix_convolution_run {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ)
    (count output : List Bool) (hc : count.length = j + 1) (regs : Fin 6 → Bool) :
    ∃ finalRegs, Trace prefixReverseProgram (7 * (j + 1) + 3)
      (prefixCfg (some 0) regs
        (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) a)
        count output)
      (prefixCfg none finalRegs (coefficientArray ((List.ofFn a).drop (j + 1))) []
        (coefficientArray (convolutionRight a j) ++ output)) := by
  have he := prefixReverse_trace (List.ofFn a) count output regs
  simpa only [hc, coefficientArray_ofFn, paddedPrefix_convolutionRight] using he

/-- A second paid prefix pass reverses the left stream back into ascending
coefficient order. Its count is the same runtime unary word. -/
theorem prefix_convolutionLeft_run {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ)
    (count output : List Bool) (hc : count.length = j + 1) (regs : Fin 6 → Bool) :
    ∃ finalRegs, Trace prefixReverseProgram (7 * (j + 1) + 3)
      (prefixCfg (some 0) regs (coefficientArray (convolutionRight a j)) count output)
      (prefixCfg none finalRegs [] [] (coefficientArray (convolutionLeft a j) ++ output)) := by
  have hl : (convolutionRight a j).length = j + 1 := by simp [convolutionRight]
  have hr : (convolutionRight a j).reverse = convolutionLeft a j := by
    rw [← reverse_convolutionLeft, List.reverse_reverse]
  have he := prefixReverse_trace (convolutionRight a j) count output regs
  rw [hc, paddedPrefix_of_length _ _ hl, hr] at he
  simpa [List.drop_eq_nil_iff.mpr (by omega : (convolutionRight a j).length ≤ j + 1)] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
