import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext

namespace OAI.Algorithms

/-! Exact row-major scalar serialization for explicitly ordered row and
column lists. This is the representation bridge consumed by the executable
constraint-matrix producer. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixListEncoding

def matrix {α β : Type*} (p : ℕ) (rows : List α) (columns : List β)
    (entry : α → β → ZMod p) : Fin rows.length → Fin columns.length → ZMod p :=
  fun i j => entry (rows.get i) (columns.get j)

theorem ofFn_get_map {α β : Type*} (xs : List α) (f : α → β) :
    List.ofFn (fun i : Fin xs.length => f (xs.get i)) = xs.map f := by
  change List.ofFn (f ∘ xs.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem matrixRows {α β : Type*} (p : ℕ) (rows : List α) (columns : List β)
    (entry : α → β → ZMod p) :
    BlockCoefficientProgram.matrixRows p (matrix p rows columns entry) =
      rows.map (fun row => columns.map (fun col => MatrixWordEncoding.word p (entry row col))) := by
  change List.ofFn (fun i : Fin rows.length => List.ofFn (fun j : Fin columns.length =>
    MatrixWordEncoding.word p (entry (rows.get i) (columns.get j)))) = _
  have hcolumn (row : α) :
      List.ofFn (fun j : Fin columns.length => MatrixWordEncoding.word p (entry row (columns.get j))) =
        columns.map (fun col => MatrixWordEncoding.word p (entry row col)) :=
    ofFn_get_map columns (fun col => MatrixWordEncoding.word p (entry row col))
  simp_rw [hcolumn]
  exact ofFn_get_map rows (fun row => columns.map (fun col => MatrixWordEncoding.word p (entry row col)))

theorem words_eq_flatMap (xs : List (List Bool)) :
    MatrixProgramSupport.words xs = xs.flatMap Encoding.frame := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [MatrixProgramSupport.words, ih]

theorem matrixBits {α β : Type*} (p : ℕ) (rows : List α) (columns : List β)
    (entry : α → β → ZMod p) :
    BlockCoefficientProgram.matrixBits p (matrix p rows columns entry) =
      rows.flatMap (fun row => columns.flatMap (fun col =>
        Encoding.frame (MatrixWordEncoding.word p (entry row col)))) := by
  rw [BlockCoefficientProgram.matrixBits, matrixRows]
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons]
      rw [MatrixProgramSupport.words_append, ih, words_eq_flatMap, List.flatMap_map]

theorem sigma_flatMap {ι γ : Type*} {α : ι → Type*}
    (indices : List ι) (rows : ∀ i, List (α i)) (f : ((i : ι) × α i) → List γ) :
    (indices.sigma rows).flatMap f =
      indices.flatMap (fun i => (rows i).flatMap (fun x => f ⟨i, x⟩)) := by
  simp [List.sigma, List.flatMap_assoc, List.flatMap_map]

end SubexponentialSAT.Subexp.ConstraintMatrixListEncoding

end OAI.Algorithms
