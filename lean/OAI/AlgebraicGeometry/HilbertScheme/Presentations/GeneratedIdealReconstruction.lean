import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedDegreeRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal

/-! # Generated Ideal Reconstruction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedIdealReconstruction.GradedHilbert

noncomputable section

/-! An ideal generated in one degree is recovered from its relations in that
degree, over every coefficient ring. -/

open _root_.MvPolynomial

universe u v
variable {R : Type u} [CommRing R] {n N : ℕ} {ι : Type v}

theorem degreeGeneratedIdeal_homogeneousGenerators
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hg : ∀ i, (g i).IsHomogeneous N) :
    DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) N =
      Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg := by
  apply HomogeneousIdeal.toIdeal_injective
  apply le_antisymm (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_le _ _)
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact DegreeGeneratedIdeal.GradedHilbert.mem_degreeGeneratedIdeal _ _ (g i) (hg i) (Ideal.subset_span (Set.mem_range_self i))

theorem homogeneousGeneratorsIdeal_eq_of_degreeRelations_eq
    {κ : Type*} (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (h : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)
    (hg : ∀ i, (g i).IsHomogeneous N) (hh : ∀ i, (h i).IsHomogeneous N)
    (he : Hilbert.Polynomial.GradedHilbert.degreeRelations (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal N =
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h N hh).toIdeal N) :
    Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg = Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h N hh := by
  have h' := DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_eq_of_degreeRelations_eq _ _ N he
  simpa only [degreeGeneratedIdeal_homogeneousGenerators] using h'

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedIdealReconstruction.GradedHilbert
