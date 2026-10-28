import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.FiniteSubsets
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Signs
import Mathlib.Order.Interval.Finset.Fin

/-! # Subset Signs -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SubsetSigns

noncomputable section

/-! Ordered-tuple positions give exactly the finite-subset Čech signs. -/

universe u v

variable {ι : Type u} [LinearOrder ι]

theorem orderedCechIndexFinset_filter_card {q : ℕ} (a : Ordered.SectionCechIndices.OrderedCechIndex ι q) (k : Fin (q + 1)) :
    ((FiniteSubsets.orderedCechIndexFinset a).filter (· < a.val k)).card = k.val := by
  have he : (FiniteSubsets.orderedCechIndexFinset a).filter (· < a.val k) = (Finset.Iio k).image a.val := by
    ext x
    simp only [FiniteSubsets.orderedCechIndexFinset, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, a.property.lt_iff_lt.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, a.property hj⟩
  rw [he, Finset.card_image_of_injective _ a.property.injective, Fin.card_Iio]

theorem orderedCechIndexFinset_sign (R : Type v) [CommRing R]
    {q : ℕ} (a : Ordered.SectionCechIndices.OrderedCechIndex ι q) (k : Fin (q + 1)) :
    HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign R (FiniteSubsets.orderedCechIndexFinset a) (a.val k) =
      (-1 : R) ^ k.val := by
  unfold HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign
  rw [orderedCechIndexFinset_filter_card]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SubsetSigns
