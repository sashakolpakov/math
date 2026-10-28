import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularGroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.IdempotentGroupProduct

/-! # Upper Unipotent Block Retraction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnipotentBlockRetraction.Construction

noncomputable section

/-! Projection to equal-weight blocks is a continuous retraction
of the upper unipotent group and supplies product coordinates. -/

open scoped Classical

def upperUnitriangularBlockProjection {n : ℕ} (w : Fin n → ℝ) (hw : Antitone w) :
    UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n →* UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n where
  toFun g := ⟨FilteredMatrixUnitProjection.Construction.weightBlockUnitProjection w (UpperUnitriangularGroup.Construction.upperUnitriangularFilteredHom w hw g),
    UpperUnitriangularGroup.Construction.weightBlockProjection_upper_unitriangular w g.val.val g.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one ((FilteredMatrixUnitProjection.Construction.weightBlockUnitProjection w).comp (UpperUnitriangularGroup.Construction.upperUnitriangularFilteredHom w hw))
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul ((FilteredMatrixUnitProjection.Construction.weightBlockUnitProjection w).comp (UpperUnitriangularGroup.Construction.upperUnitriangularFilteredHom w hw)) g h

theorem upperUnitriangularBlockProjection_val {n : ℕ} (w : Fin n → ℝ) (hw : Antitone w)
    (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n) :
    (upperUnitriangularBlockProjection w hw g).val.val = Weight.BlockProjection.Construction.weightBlockProjection w g.val.val := rfl

theorem upperUnitriangularBlockProjection_continuous {n : ℕ} (w : Fin n → ℝ) (hw : Antitone w) :
    Continuous (upperUnitriangularBlockProjection w hw) := by
  have hi : Continuous (UpperUnitriangularGroup.Construction.upperUnitriangularFilteredHom w hw) := continuous_subtype_val.subtype_mk _
  exact ((FilteredMatrixUnitProjection.Construction.weightBlockUnitProjection_continuous w).comp hi).subtype_mk _

theorem upperUnitriangularBlockProjection_idempotent {n : ℕ} (w : Fin n → ℝ) (hw : Antitone w)
    (g : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n) :
    upperUnitriangularBlockProjection w hw (upperUnitriangularBlockProjection w hw g) =
      upperUnitriangularBlockProjection w hw g := by
  apply Subtype.ext
  apply Units.ext
  exact Weight.BlockProjection.Construction.weightBlockProjection_idempotent w g.val.val

def upperUnitriangularBlockProductHomeomorph {n : ℕ} (w : Fin n → ℝ) (hw : Antitone w) :
    (upperUnitriangularBlockProjection w hw).range × (upperUnitriangularBlockProjection w hw).ker ≃ₜ
      UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup n :=
  IdempotentGroupProduct.Construction.idempotentGroupProductHomeomorph (upperUnitriangularBlockProjection w hw)
    (upperUnitriangularBlockProjection_continuous w hw) (upperUnitriangularBlockProjection_idempotent w hw)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnipotentBlockRetraction.Construction
