import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithmEntry
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryEvaluation

namespace OAI.Algorithms

/-! The original fixed-control four-word scan classifies the new integer
numerator too. Only its final scalar arithmetic changes: the read result is
fed to the exact integer formula, not to the old finite-field formula. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixScanProgram SubexponentialSAT.Subexp.MatrixEntryEvaluation
open SubexponentialSAT.Subexp.MatrixEntryKernel

variable {r Q : ℕ}

def integerFromScan (A R : ℕ) (d : SubexponentialSAT.Subexp.MatrixScanProgram.Data) : ℤ :=
  if d.regs 7 then LayoutCoefficientAlgorithm.scalarSum A R
    ((d.stacks 2).length - 1) (d.stacks 3).length else 0

private theorem single_spectator (u y : UniversalType r Q 1) :
    SpectatorsAgree (0 : Fin 1) u y := by
  intro j hj
  exact (hj (Subsingleton.elim j 0)).elim

/-- The compatibility bit is exactly the guard of the literal integer formula;
the two unary counters are its distance and transposition parameters. -/
theorem integerFromScan_correct (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g (0 : Fin 1)) (a : SubexponentialSAT.Subexp.MatrixScanProgram.Data)
    (hflag : a.regs 7 = true) (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = []) :
    integerFromScan A R (result (rows 0 u.val y.val) a) =
      LayoutNumerator.joint (0 : Fin 1) t g A R u y := by
  have hc : (rows (0 : Fin 1) u.val y.val).all compatible =
      decide (AllCompatible (0 : Fin 1) u.val y.val) := by
    simpa [single_spectator u.val y.val] using compatibility_rows (0 : Fin 1) u.val y.val
  have hbit : (result (rows (0 : Fin 1) u.val y.val) a).regs 7 =
      decide (AllCompatible (0 : Fin 1) u.val y.val) := by
    rw [result_compatible, hflag, Bool.true_and, hc]
  unfold integerFromScan
  rw [hbit, result_count2, result_count3, h2, h3]
  simp only [List.append_nil, List.length_replicate]
  rw [unchangedCount_rows, transposedCount_rows]
  unfold LayoutNumerator.joint
  rw [← LayoutCoefficientAlgorithm.scalarEntry_eq_entry]
  unfold LayoutCoefficientAlgorithm.scalarEntry
  by_cases h : AllCompatible (0 : Fin 1) u.val y.val
  · have h' := (allCompatible_iff_joint (0 : Fin 1) t g u y).mp h
    rw [allUnchanged_card_joint (0 : Fin 1) t g u y h,
      allTransposed_eq_joint (0 : Fin 1) t g u y]
    simp [h, h']
  · have h' : ¬ Compatible (0 : Fin 1) t u.val y.val :=
      fun hc => h ((allCompatible_iff_joint (0 : Fin 1) t g u y).mpr hc)
    simp [h, h']

/-- Concrete finite bit execution of the classification stage. `integerFromScan`
is the next stage's specification; it is not executed as a machine primitive. -/
theorem classifyInteger_runsIn (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g (0 : Fin 1)) (a : SubexponentialSAT.Subexp.MatrixScanProgram.Data)
    (ready : Ready a (rows 0 u.val y.val) r)
    (hflag : a.regs 7 = true) (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = []) :
    RunsIn program (Q * (208 * r + 149) + 3)
      (a.withPC (some program.entry))
      ((result (rows 0 u.val y.val) a).withPC none) ∧
    integerFromScan A R (result (rows 0 u.val y.val) a) =
      LayoutNumerator.joint (0 : Fin 1) t g A R u y := by
  constructor
  · simpa using program_runsIn a (rows 0 u.val y.val) r ready
  · exact integerFromScan_correct A R t g u y a hflag h2 h3

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
