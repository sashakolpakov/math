import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.OverlapCoordinates

/-! # Row Column Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.RowColumnTransitions

noncomputable section

/-! Row and column normalizations on Segre chart intersections differ by units. -/

universe u v w

variable (R : Type u) [CommRing R] {σ : Type v} {τ : Type w} (p q : σ × τ)

theorem segreOverlap_rowPivot_isUnit :
    IsUnit (OverlapCoordinates.segreOverlapCoordinateLeft R p q (q.1, p.2)) := by
  have h := OverlapCoordinates.segreOverlapCoordinate_pivot_isUnit R p q
  rw [show q = (q.1, q.2) from rfl, OverlapCoordinates.segreOverlapCoordinateLeft_entry] at h
  exact isUnit_of_mul_isUnit_left h

theorem segreOverlap_columnPivot_isUnit :
    IsUnit (OverlapCoordinates.segreOverlapCoordinateLeft R p q (p.1, q.2)) := by
  have h := OverlapCoordinates.segreOverlapCoordinate_pivot_isUnit R p q
  rw [show q = (q.1, q.2) from rfl, OverlapCoordinates.segreOverlapCoordinateLeft_entry] at h
  exact isUnit_of_mul_isUnit_right h

theorem segreOverlap_rowCross (a : σ) :
    OverlapCoordinates.segreOverlapCoordinateLeft R p q (q.1, p.2) *
      OverlapCoordinates.segreOverlapCoordinateRight R p q (a, q.2) =
        OverlapCoordinates.segreOverlapCoordinateLeft R p q (a, p.2) := by
  apply (segreOverlap_columnPivot_isUnit R p q).mul_left_cancel
  calc
    _ = (OverlapCoordinates.segreOverlapCoordinateLeft R p q (q.1, p.2) *
        OverlapCoordinates.segreOverlapCoordinateLeft R p q (p.1, q.2)) *
          OverlapCoordinates.segreOverlapCoordinateRight R p q (a, q.2) := by ring
    _ = OverlapCoordinates.segreOverlapCoordinateLeft R p q q *
        OverlapCoordinates.segreOverlapCoordinateRight R p q (a, q.2) := by
      rw [← OverlapCoordinates.segreOverlapCoordinateLeft_entry]
    _ = OverlapCoordinates.segreOverlapCoordinateLeft R p q (a, q.2) := OverlapCoordinates.segreOverlapCoordinate_cross R p q _
    _ = OverlapCoordinates.segreOverlapCoordinateLeft R p q (a, p.2) *
        OverlapCoordinates.segreOverlapCoordinateLeft R p q (p.1, q.2) := OverlapCoordinates.segreOverlapCoordinateLeft_entry R p q _ _
    _ = _ := mul_comm _ _

theorem segreOverlap_columnCross (b : τ) :
    OverlapCoordinates.segreOverlapCoordinateLeft R p q (p.1, q.2) *
      OverlapCoordinates.segreOverlapCoordinateRight R p q (q.1, b) =
        OverlapCoordinates.segreOverlapCoordinateLeft R p q (p.1, b) := by
  apply (segreOverlap_rowPivot_isUnit R p q).mul_left_cancel
  calc
    _ = (OverlapCoordinates.segreOverlapCoordinateLeft R p q (q.1, p.2) *
        OverlapCoordinates.segreOverlapCoordinateLeft R p q (p.1, q.2)) *
          OverlapCoordinates.segreOverlapCoordinateRight R p q (q.1, b) := by ring
    _ = OverlapCoordinates.segreOverlapCoordinateLeft R p q q *
        OverlapCoordinates.segreOverlapCoordinateRight R p q (q.1, b) := by
      rw [← OverlapCoordinates.segreOverlapCoordinateLeft_entry]
    _ = OverlapCoordinates.segreOverlapCoordinateLeft R p q (q.1, b) := OverlapCoordinates.segreOverlapCoordinate_cross R p q _
    _ = _ := OverlapCoordinates.segreOverlapCoordinateLeft_entry R p q _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.RowColumnTransitions
