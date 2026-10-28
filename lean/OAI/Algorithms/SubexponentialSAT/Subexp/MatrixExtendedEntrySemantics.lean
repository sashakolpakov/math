import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorTypes
import OAI.Algorithms.SubexponentialSAT.Subexp.ElementaryMatrix
import OAI.Algorithms.SubexponentialSAT.SubexpAnnihilation

namespace OAI.Algorithms

/-! Exact joint-membership meaning of the three selected-color comparisons. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open MulticolorTypes

variable {r Q Δ : ℕ}

def anchorValid (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) : Prop :=
  u.head t = y.head t ∧ u.slot i t ≠ y.head t ∧ y.slot i t ≠ y.head t

instance (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    Decidable (anchorValid i t u y) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem anchorValid_iff_joint (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    anchorValid i t u y ↔ u ∈ joint t (y.head t) i ∧ y ∈ joint t (y.head t) i := by
  simp [anchorValid, and_assoc]

theorem selected_colors_valid (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    (MatrixAnchorReadProgram.colorWord (u.head t) = MatrixAnchorReadProgram.colorWord (y.head t) ∧
      MatrixAnchorReadProgram.colorWord (u.slot i t) ≠ MatrixAnchorReadProgram.colorWord (y.head t) ∧
      MatrixAnchorReadProgram.colorWord (y.slot i t) ≠ MatrixAnchorReadProgram.colorWord (y.head t)) ↔
      anchorValid i t u y := by
  simp [anchorValid]

theorem zeroExtend_of_valid {K : Type*} [Ring K] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (M : Matrix (Joint t (y.head t) i) (Joint t (y.head t) i) K)
    (h : anchorValid i t u y) :
    SubexpAnnihilation.zeroExtendMatrix (joint t (y.head t) i) M u y =
      M ⟨u, h.1, h.2.1⟩ ⟨y, rfl, h.2.2⟩ := by
  simp [SubexpAnnihilation.zeroExtendMatrix, show u ∈ joint t (y.head t) i from ⟨h.1, h.2.1⟩,
    show y ∈ joint t (y.head t) i from ⟨rfl, h.2.2⟩]

theorem zeroExtend_of_invalid {K : Type*} [Ring K] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (M : Matrix (Joint t (y.head t) i) (Joint t (y.head t) i) K)
    (h : ¬ anchorValid i t u y) :
    SubexpAnnihilation.zeroExtendMatrix (joint t (y.head t) i) M u y = 0 := by
  by_cases hu : u ∈ joint t (y.head t) i
  · have hy : y ∉ joint t (y.head t) i := by
      intro hy
      exact h ((anchorValid_iff_joint i t u y).mpr ⟨hu, hy⟩)
    exact SubexpAnnihilation.zeroExtendMatrix_of_column_not_mem _ _ _ _ hy
  · exact SubexpAnnihilation.zeroExtendMatrix_of_row_not_mem _ _ _ _ hu

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
