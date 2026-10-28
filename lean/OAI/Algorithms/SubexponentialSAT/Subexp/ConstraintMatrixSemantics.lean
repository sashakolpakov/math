import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntries
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixListEncoding

namespace OAI.Algorithms

/-! The bytes emitted in the actual Side/Joint order encode the same linear
constraint map used in the kernel proof. No reordering or replacement by a
canonical precomputed matrix is involved. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixProgram

open MulticolorTypes MatrixWordEncoding

variable {r Q Δ : ℕ}

theorem sideBytes_length (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (TypeEnumeration.sideBytes r Q Δ t.val g.val).length =
      (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length := by
  rw [← TypeEnumeration.sideList_bytes hr hQ t g]
  simp

noncomputable def rowList (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    List ((i : Fin Δ) × Joint t g i) :=
  (List.finRange Δ).sigma (TypeEnumeration.jointList hr hQ t g)

theorem rowList_nodup (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (rowList (Δ := Δ) hr hQ t g).Nodup :=
  (List.nodup_finRange Δ).sigma (TypeEnumeration.jointList_nodup hr hQ t g)

theorem mem_rowList (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (u : (i : Fin Δ) × Joint t g i) : u ∈ rowList hr hQ t g :=
  List.mem_sigma.mpr ⟨List.mem_finRange u.1, TypeEnumeration.mem_jointList hr hQ t g u.1 u.2⟩

noncomputable def rowEquiv (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    Fin (rowList (Δ := Δ) hr hQ t g).length ≃ ((i : Fin Δ) × Joint t g i) :=
  List.Nodup.getEquivOfForallMemList _ (rowList_nodup hr hQ t g) (mem_rowList hr hQ t g)

theorem sigma_length {α : Type*} {β : α → Type*} (is : List α) (xs : ∀ i, List (β i)) :
    (is.sigma xs).length = (is.map (fun i => (xs i).length)).sum := by
  induction is with
  | nil => simp
  | cons i is ih => simp [List.sigma_cons, ih]

theorem rowList_length (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (rowList (Δ := Δ) hr hQ t g).length = rowCount (Δ := Δ) hr hQ t g := by
  rw [rowList, sigma_length]
  simp [rowCount, rows, List.ofFn_eq_map]

noncomputable def matrix (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) :
    Fin (rowList (Δ := Δ) hr hQ t g).length →
      Fin (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length → ZMod p := fun a b =>
  let row := rowEquiv hr hQ t g a
  let col := TypeEnumeration.sideEquiv hr hQ t g b
  ConstraintEntryProgram.value p row.1 t row.2.val col.val coefficients

theorem value_on_fibers (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u : Joint t g i) (y : Side (Δ := Δ) t g) (coefficients : List (ZMod p)) :
    ConstraintEntryProgram.value p i t u.val y.val coefficients =
      (if u.val = y.val then 1 else 0) -
        if hy : y.val ∈ joint t g i then
          ElementaryMatrix.jointMatrixDP i t g coefficients.length
            (fun j => coefficients.getD j 0 * (2 : ZMod p)^j) u ⟨y.val, hy⟩
        else 0 := by
  have hyhead : y.val.head t = g := y.property
  unfold ConstraintEntryProgram.value MatrixExtendedEntryProgram.value
  rw [hyhead]
  simp only [SubexpAnnihilation.zeroExtendMatrix, dite_eq_left u.property]

theorem matrix_eq_constraints (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) :
    matrix (Δ := Δ) p hr hQ t g coefficients =
      SubspaceDimension.encodedConstraintMatrix (side t g) (fun i => joint t g i)
        (fun i => joint_subset_side t g i)
        (fun i => (ElementaryMatrix.jointMatrixDP i t g coefficients.length
          (fun j => coefficients.getD j 0 * (2 : ZMod p)^j)).mulVecLin)
        (rowEquiv hr hQ t g) (TypeEnumeration.sideEquiv hr hQ t g) := by
  funext a b
  rw [← ConstraintEntries.joint_entry_eq]
  exact value_on_fibers p (rowEquiv hr hQ t g a).1 t g
    (rowEquiv hr hQ t g a).2 (TypeEnumeration.sideEquiv hr hQ t g b) coefficients

theorem matrix_rows (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) :
    BlockCoefficientProgram.matrixRows p (matrix (Δ := Δ) p hr hQ t g coefficients) =
      (rowList (Δ := Δ) hr hQ t g).map fun row =>
        (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).map fun col =>
          word p (ConstraintEntryProgram.value p row.1 t row.2.val col.val coefficients) := by
  exact ConstraintMatrixListEncoding.matrixRows p (rowList (Δ := Δ) hr hQ t g)
    (TypeEnumeration.sideList (Δ := Δ) hr hQ t g)
    (fun row col => ConstraintEntryProgram.value p row.1 t row.2.val col.val coefficients)

theorem matrixBytes_eq (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) :
    matrixBytes (Δ := Δ) p hr hQ t g coefficients =
      BlockCoefficientProgram.matrixBits p (matrix (Δ := Δ) p hr hQ t g coefficients) := by
  change matrixBytes (Δ := Δ) p hr hQ t g coefficients =
    BlockCoefficientProgram.matrixBits p
      (ConstraintMatrixListEncoding.matrix p (rowList (Δ := Δ) hr hQ t g)
        (TypeEnumeration.sideList (Δ := Δ) hr hQ t g)
        (fun row col => ConstraintEntryProgram.value p row.1 t row.2.val col.val coefficients))
  rw [ConstraintMatrixListEncoding.matrixBits, rowList, ConstraintMatrixListEncoding.sigma_flatMap]
  simp [matrixBytes, List.ofFn_eq_map, List.flatMap_def]
  rfl

@[simp] theorem output_matrix (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (regs : Fin 18 → Bool) :
    (output (Δ := Δ) p hr hQ t g coefficients regs).stacks 0 =
      BlockCoefficientProgram.matrixBits p (matrix (Δ := Δ) p hr hQ t g coefficients) := by
  simpa only [output, Function.update_self] using matrixBytes_eq p hr hQ t g coefficients

@[simp] theorem output_rows (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (regs : Fin 18 → Bool) :
    (output (Δ := Δ) p hr hQ t g coefficients regs).stacks 55 =
      List.replicate (rowList (Δ := Δ) hr hQ t g).length true := by
  simp [output, state, rowList_length]

@[simp] theorem output_side (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (regs : Fin 18 → Bool) :
    (output (Δ := Δ) p hr hQ t g coefficients regs).stacks 53 =
      ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t.val g.val) := by
  simp [output, state]

end SubexponentialSAT.Subexp.ConstraintMatrixProgram

end OAI.Algorithms
