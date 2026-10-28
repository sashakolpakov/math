import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPascalRefinement
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryScalar

namespace OAI.Algorithms

/-! Connect the concrete scan counters and adjacent-add value to the actual
joint matrix. These are refinement lemmas for the physical component programs,
not alternative definitions of their runtime instructions. -/

namespace SubexponentialSAT.Subexp.MatrixEntryEvaluation

open MulticolorTypes MatrixScanProgram
open scoped BigOperators

variable {r Q Δ : ℕ}

def rows (i : Fin Δ) (u y : UniversalType r Q Δ) : List ColorRow :=
  List.ofFn (typedRow i u y)

@[simp] theorem rows_length (i : Fin Δ) (u y : UniversalType r Q Δ) :
    (rows i u y).length = Q := by simp [rows]

theorem rows_width (i : Fin Δ) (u y : UniversalType r Q Δ) :
    ∀ w ∈ rows i u y, ∀ j, (w j).length = r := by
  intro w hw j
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hw
  exact typedRow_length i u y l j

theorem rows_streams (i : Fin Δ) (u y : UniversalType r Q Δ) :
    streams (rows i u y) =
      ![ReadPlan.encodeWord u.head, ReadPlan.encodeWord (u.slot i),
        ReadPlan.encodeWord y.head, ReadPlan.encodeWord (y.slot i)] := by
  funext j
  fin_cases j <;> simp [streams, rows, Function.comp_def, typedRow, encodeColor, ReadPlan.encodeWord]

theorem unchangedCount_sum (ws : List ColorRow) :
    unchangedCount ws = (ws.map (fun w => if same w && !swapped w then 1 else 0)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [unchangedCount, ih, Nat.add_comm]

theorem transposedCount_sum (ws : List ColorRow) :
    transposedCount ws = (ws.map (fun w => if swapped w && !same w then 1 else 0)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [transposedCount, ih, Nat.add_comm]

theorem same_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using same_typedRow i u y l

theorem swapped_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide ((u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using swapped_typedRow i u y l

theorem unchanged_test (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (same (typedRow i u y l) && !swapped (typedRow i u y l)) =
      decide (u.head l ≠ u.slot i l ∧ MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) := by
  apply Bool.eq_iff_iff.mpr
  simpa [same_pair, swapped_pair] using MatrixEntryKernel.same_not_swap_iff i u y l

theorem transposed_test (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (swapped (typedRow i u y l) && !same (typedRow i u y l)) =
      decide (u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) := by
  apply Bool.eq_iff_iff.mpr
  simpa [same_pair, swapped_pair] using MatrixEntryKernel.swap_not_same_iff i u y l

theorem unchangedCount_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    unchangedCount (rows i u y) = (MatrixEntryKernel.allUnchanged i u y).card := by
  rw [unchangedCount_sum]
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_def, unchanged_test, decide_eq_true_eq]
  simp [MatrixEntryKernel.allUnchanged]

theorem transposedCount_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    transposedCount (rows i u y) = (MatrixEntryKernel.allTransposed i u y).card := by
  rw [transposedCount_sum]
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_def, transposed_test, decide_eq_true_eq]
  simp [MatrixEntryKernel.allTransposed]

theorem compatibility_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    (decide (MatrixEntryKernel.SpectatorsAgree i u y) && (rows i u y).all compatible) =
      decide (MatrixEntryKernel.AllCompatible i u y) := by
  apply Bool.eq_iff_iff.mpr
  simp [rows, compatible, same_pair, swapped_pair, List.all_eq_true,
    MatrixEntryKernel.AllCompatible, decide_eq_true_eq]
  by_cases h : MatrixEntryKernel.SpectatorsAgree i u y ∧
      ∀ a : Fin Q, MatrixEntryKernel.pair i u a = MatrixEntryKernel.pair i y a ∨
        (u.slot i a, u.head a) = MatrixEntryKernel.pair i y a
  · simp [h]
  · simp [h]

theorem unchangedCount_le (i : Fin Δ) (u y : UniversalType r Q Δ) :
    unchangedCount (rows i u y) ≤ Q := by
  rw [unchangedCount_rows]
  have h := Finset.card_le_card (Finset.filter_subset
    (fun l : Fin Q => u.head l ≠ u.slot i l ∧
      MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) Finset.univ)
  simpa [MatrixEntryKernel.allUnchanged] using h

theorem transposedCount_le (i : Fin Δ) (u y : UniversalType r Q Δ) :
    transposedCount (rows i u y) ≤ Q := by
  rw [transposedCount_rows]
  have h := Finset.card_le_card (Finset.filter_subset
    (fun l : Fin Q => u.head l ≠ u.slot i l ∧
      (u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) Finset.univ)
  simpa [MatrixEntryKernel.allTransposed] using h

/-- The anchor decrement in the positive branch consumes a real token. -/
theorem unchangedCount_pos_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) (h : MatrixEntryKernel.AllCompatible i u.val y.val) :
    0 < unchangedCount (rows i u.val y.val) := by
  rw [unchangedCount_rows, MatrixEntryKernel.allUnchanged_card_joint i t g u y h]
  omega

variable (p : ℕ) [Fact p.Prime]

/-- The unpadded coefficient list gives exactly the normalized joint entry. -/
theorem joint_entry (h2 : (2 : ZMod p) ≠ 0) (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (xs : List (ZMod p)) (u y : Joint t g i) :
    ElementaryMatrix.jointMatrixDP i t g xs.length
        (fun j => xs.getD j 0 * (2 : ZMod p)^j) u y =
      if decide (MatrixEntryKernel.SpectatorsAgree i u.val y.val) &&
          (rows i u.val y.val).all compatible then
        (-1 : ZMod p)^(unchangedCount (rows i u.val y.val) - 1) *
          (MatrixPascalProgram.repeated p (transposedCount (rows i u.val y.val)) xs).getD
            (unchangedCount (rows i u.val y.val) - 1) 0
      else 0 := by
  rw [MatrixEntryKernel.jointMatrixDP_all_normalized h2, compatibility_rows,
    unchangedCount_rows, transposedCount_rows, MatrixPascalProgram.repeated_getD]
  simp

theorem joint_entry_padded (h2 : (2 : ZMod p) ≠ 0) (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (xs : List (ZMod p)) (padding : ℕ) (u y : Joint t g i) :
    ElementaryMatrix.jointMatrixDP i t g xs.length
        (fun j => xs.getD j 0 * (2 : ZMod p)^j) u y =
      if decide (MatrixEntryKernel.SpectatorsAgree i u.val y.val) &&
          (rows i u.val y.val).all compatible then
        (-1 : ZMod p)^(unchangedCount (rows i u.val y.val) - 1) *
          (MatrixPascalProgram.repeated p (transposedCount (rows i u.val y.val))
            (xs ++ List.replicate padding 0)).getD
              (unchangedCount (rows i u.val y.val) - 1) 0
      else 0 := by
  rw [MatrixPascalProgram.repeated_zeroPad_getD]
  exact joint_entry p h2 i t g xs u y

end SubexponentialSAT.Subexp.MatrixEntryEvaluation

end OAI.Algorithms
