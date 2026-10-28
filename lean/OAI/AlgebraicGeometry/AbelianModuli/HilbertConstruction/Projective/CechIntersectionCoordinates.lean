import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.LiftedIndices
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CommonCoordinateOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.RestrictionCoordinates

/-! # Cech Intersection Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechIntersectionCoordinates

noncomputable section

/-! Each actual ordered projective Čech intersection is its matching multi-coordinate localization chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveCechIndexFinset {q : ℕ} (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) :
    Finset (Fin (n + 1)) :=
  OrderedCech.FiniteSubsets.orderedCechIndexFinset (OrderedCech.LiftedIndices.orderedCechIndexULiftEquiv (Fin (n + 1)) q a)

theorem projectiveCechIndexFinset_mem {q : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) (k : Fin (q + 1)) :
    (a.val k).down ∈ projectiveCechIndexFinset a :=
  Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

theorem projectiveCechIndexFinset_card {q : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) :
    (projectiveCechIndexFinset a).card = q + 1 :=
  OrderedCech.FiniteSubsets.orderedCechIndexFinset_card (OrderedCech.LiftedIndices.orderedCechIndexULiftEquiv (Fin (n + 1)) q a)

theorem projectiveCechIndexFinset_delete {q : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) (q + 1)) (k : Fin (q + 2)) :
    projectiveCechIndexFinset (a.delete k) = (projectiveCechIndexFinset a).erase (a.val k).down :=
  OrderedCech.FiniteSubsets.orderedCechIndexFinset_delete (OrderedCech.LiftedIndices.orderedCechIndexULiftEquiv (Fin (n + 1)) (q + 1) a) k

theorem projectiveCechIntersection_eq_chart {q : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) :
    (∏ᶜ fun k : Fin (q + 1) ↦ CechCover.projectiveCechOpens I (a.val k)) =
      ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I (projectiveCechIndexFinset a) := by
  rw [Affine.CechIntersections.opensProduct_eq_iInf]
  apply le_antisymm
  · apply CommonCoordinateOpen.le_coordinateProjectiveChartOpen
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact iInf_le _ k
  · apply le_iInf
    intro k
    exact ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I
      (Finset.singleton_subset_iff.mpr (projectiveCechIndexFinset_mem a k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechIntersectionCoordinates
