import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithmEntry
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryEvaluation
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntrySemantics

namespace OAI.Algorithms

/-! Convert the paid all-coordinate classifier's counters to the literal
integer matrix entry after the paid anchor guard succeeds. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixScanProgram SubexponentialSAT.Subexp.MatrixEntryEvaluation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q : ℕ}

/-- The physical scan includes the anchor; its unchanged count therefore loses
exactly one token before the scalar preparation program is called. -/
theorem scanFormula_eq_scalarEntry (A R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1) (ha : anchorValid (0 : Fin 1) t u y) :
    (if AllCompatible (0 : Fin 1) u y then
      LayoutCoefficientAlgorithm.scalarSum A R
        (unchangedCount (rows (0 : Fin 1) u y)-1)
        (transposedCount (rows (0 : Fin 1) u y)) else 0) =
      LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y := by
  have hj := (anchorValid_iff_joint (0 : Fin 1) t u y).mp ha
  let uj : Joint t (y.head t) (0 : Fin 1) := ⟨u,hj.1⟩
  let yj : Joint t (y.head t) (0 : Fin 1) := ⟨y,hj.2⟩
  have hi : AllCompatible (0 : Fin 1) u y ↔ Compatible (0 : Fin 1) t u y :=
    allCompatible_iff_joint (0 : Fin 1) t (y.head t) uj yj
  rw [unchangedCount_rows,transposedCount_rows]
  unfold LayoutCoefficientAlgorithm.scalarEntry
  by_cases hc : AllCompatible (0 : Fin 1) u y
  · have hc' := hi.mp hc
    rw [ite_eq_left hc,ite_eq_left hc',
      allUnchanged_card_joint (0 : Fin 1) t (y.head t) uj yj hc,
      allTransposed_eq_joint (0 : Fin 1) t (y.head t) uj yj]
    simp [uj,yj]
  · have hc' : ¬ Compatible (0 : Fin 1) t u y := fun h => hc (hi.mpr h)
    simp [hc,hc']

/-- A compatible guarded row always supplies an anchor token, and both physical
counters are bounded by the number of scanned coordinates. -/
theorem scanCounts_bounds_of_anchor (t : Fin Q) (u y : UniversalType r Q 1)
    (ha : anchorValid (0 : Fin 1) t u y) (hc : AllCompatible (0 : Fin 1) u y) :
    0 < unchangedCount (rows (0 : Fin 1) u y) ∧
      unchangedCount (rows (0 : Fin 1) u y) ≤ Q ∧
      transposedCount (rows (0 : Fin 1) u y) ≤ Q := by
  have hj := (anchorValid_iff_joint (0 : Fin 1) t u y).mp ha
  exact ⟨unchangedCount_pos_joint (0 : Fin 1) t (y.head t)
      ⟨u,hj.1⟩ ⟨y,hj.2⟩ hc,
    unchangedCount_le (0 : Fin 1) u y,transposedCount_le (0 : Fin 1) u y⟩

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
