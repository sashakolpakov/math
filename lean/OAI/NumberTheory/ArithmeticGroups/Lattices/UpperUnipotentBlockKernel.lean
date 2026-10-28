import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnipotentBlockRetraction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ProjectionKernel

/-! # Upper Unipotent Block Kernel -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnipotentBlockKernel.Construction

noncomputable section

/-! The equal-weight block retraction has precisely the strict
weight-raising kernel and the equal-weight block image. -/

open scoped Classical

theorem upperUnitriangularBlockProjection_kernel_iff {n : ℕ}
    (w : Fin n → ℝ) (hw : Antitone w) (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n) :
    g ∈ (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection w hw).ker ↔
      ∀ i j, w i ≤ w j → (g.val.val - 1) i j = 0 := by
  constructor
  · intro hg
    have he : Weight.BlockProjection.Construction.weightBlockProjection w g.val.val = 1 :=
      congrArg (fun x : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n => x.val.val) hg
    exact Weight.ProjectionKernel.Construction.matrix_filtered_projection_sub_one w g.val.val
      (UpperUnitriangularGroup.Construction.upper_triangular_ordered_weight_filtered w hw g.val.val g.property.1) he
  · intro hg
    change UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection w hw g = 1
    apply Subtype.ext
    apply Units.ext
    ext i j
    change Weight.BlockProjection.Construction.weightBlockProjection w g.val.val i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j
    rw [Weight.BlockProjection.Construction.weightBlockProjection_apply]
    by_cases hij : w i = w j
    · rw [ite_eq_left hij]
      exact sub_eq_zero.mp (hg i j hij.le)
    · rw [ite_eq_right hij, Matrix.one_apply_ne (fun he => hij (congrArg w he))]

theorem upperUnitriangularBlockProjection_range_iff {n : ℕ}
    (w : Fin n → ℝ) (hw : Antitone w) (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n) :
    g ∈ (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection w hw).range ↔
      ∀ i j, w i ≠ w j → g.val.val i j = 0 := by
  constructor
  · rintro ⟨h, rfl⟩ i j hij
    rw [UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection_val, Weight.BlockProjection.Construction.weightBlockProjection_apply, ite_eq_right hij]
  · intro hg
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    change Weight.BlockProjection.Construction.weightBlockProjection w g.val.val i j = g.val.val i j
    rw [Weight.BlockProjection.Construction.weightBlockProjection_apply]
    by_cases hij : w i = w j
    · rw [ite_eq_left hij]
    · rw [ite_eq_right hij, hg i j hij]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnipotentBlockKernel.Construction
