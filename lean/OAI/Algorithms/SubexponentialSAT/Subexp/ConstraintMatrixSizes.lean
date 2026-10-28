import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixSizeBasics

namespace OAI.Algorithms

/-! Sizes of the actual Side/Joint lists and of the bytes returned by the
one-Side matrix program. Every scalar frame is included. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixProgram

open MulticolorTypes

variable {r Q Δ : ℕ}

theorem columns_length (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (columns (Δ := Δ) hr hQ t g).length = blockSize r Q Δ / r := by
  simpa only [columns, List.length_map] using
    ConstraintMatrixSizeBasics.sideList_length (Δ := Δ) hr hQ t g

theorem rows_length (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (rows hr hQ t g i).length = (r - 1) * (blockSize r Q Δ / (r * r)) := by
  simpa only [rows, List.length_map] using
    ConstraintMatrixSizeBasics.jointList_length hr hQ t g i

theorem columns_length_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (columns (Δ := Δ) hr hQ t g).length ≤ blockSize r Q Δ := by
  simpa only [columns, List.length_map] using
    ConstraintMatrixSizeBasics.sideList_length_le (Δ := Δ) hr hQ t g

theorem rows_length_le_columns (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (rows hr hQ t g i).length ≤ (columns (Δ := Δ) hr hQ t g).length := by
  simpa only [rows, columns, List.length_map] using
    ConstraintMatrixSizeBasics.jointList_length_le_side hr hQ t g i

theorem encodedSide_length (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t.val g.val)).length =
      (columns (Δ := Δ) hr hQ t g).length *
        (2 * CollisionProgram.typeWidth r Q Δ + 2) + 1 := by
  simpa only [columns, List.length_map] using
    ConstraintMatrixSizeBasics.encodedSide_length (Δ := Δ) hr hQ t g

theorem sum_le_length_mul (ns : List ℕ) (bound : ℕ) (h : ∀ n ∈ ns, n ≤ bound) :
    ns.sum ≤ ns.length * bound := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      have hn := h n (by simp)
      have ht := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
      simp only [List.sum_cons, List.length_cons]
      calc
        n + ns.sum ≤ bound + ns.length * bound := Nat.add_le_add hn ht
        _ = (ns.length + 1) * bound := by ring

theorem rowCount_le_slots_columns (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    rowCount (Δ := Δ) hr hQ t g ≤ Δ * (columns (Δ := Δ) hr hQ t g).length := by
  have h := sum_le_length_mul (List.ofFn fun i : Fin Δ => (rows hr hQ t g i).length)
    (columns (Δ := Δ) hr hQ t g).length (by
      intro n hn
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
      exact rows_length_le_columns hr hQ t g i)
  simpa only [rowCount, List.length_ofFn] using h

theorem rowCount_le_slots_block (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    rowCount (Δ := Δ) hr hQ t g ≤ Δ * blockSize r Q Δ :=
  (rowCount_le_slots_columns hr hQ t g).trans
    (Nat.mul_le_mul_left Δ (columns_length_le hr hQ t g))

theorem matrixBytes_length (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) :
    (matrixBytes (Δ := Δ) p hr hQ t g coefficients).length =
      rowCount (Δ := Δ) hr hQ t g * (columns (Δ := Δ) hr hQ t g).length *
        (2 * MatrixWordEncoding.width p + 1) := by
  rw [matrixBytes_eq]
  change (BlockCoefficientProgram.matrixBits p
    (ConstraintMatrixListEncoding.matrix p (rowList hr hQ t g)
      (TypeEnumeration.sideList hr hQ t g)
      (fun row col => ConstraintEntryProgram.value p row.1 t row.2.val col.val coefficients))).length = _
  rw [ConstraintMatrixSizeBasics.matrixBits_length, rowList_length]
  simp only [columns, List.length_map]

theorem matrixBytes_length_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) :
    (matrixBytes (Δ := Δ) p hr hQ t g coefficients).length ≤
      Δ * (columns (Δ := Δ) hr hQ t g).length ^ 2 *
        (2 * MatrixWordEncoding.width p + 1) := by
  rw [matrixBytes_length]
  calc
    _ ≤ (Δ * (columns (Δ := Δ) hr hQ t g).length) *
        (columns (Δ := Δ) hr hQ t g).length * (2 * MatrixWordEncoding.width p + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (rowCount_le_slots_columns hr hQ t g))
    _ = _ := by ring

end SubexponentialSAT.Subexp.ConstraintMatrixProgram

end OAI.Algorithms
