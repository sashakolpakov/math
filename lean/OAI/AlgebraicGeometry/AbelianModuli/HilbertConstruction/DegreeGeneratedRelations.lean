import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.DegreeIdealRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal

/-! # Degree Generated Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeGeneratedRelations

noncomputable section

/-! The concrete single-degree ideal used in uniform projective generation satisfies the finite open-locus conditions. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ)

theorem degreeGeneratedIdeal_span_relations :
    (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N).toIdeal = Ideal.span
      ((Homogeneous.IdealIncidence.homogeneousDegreeRelations I N).map (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n N).subtype : Set (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
  apply congrArg Ideal.span
  apply Set.ext
  intro f
  constructor
  · rintro ⟨hf, hI⟩
    exact ⟨⟨f, hf⟩, hI, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.property, hp⟩

theorem degreeGeneratedIdeal_relations_below (d : ℕ) (hd : d < N) :
    Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) d = ⊥ :=
  Single.DegreeIdealRelations.singleDegreeIdeal_relations_below N (Homogeneous.IdealIncidence.homogeneousDegreeRelations I N) _
    (degreeGeneratedIdeal_span_relations I N) d hd

theorem degreeGeneratedIdeal_relations_succ (d : ℕ) (hd : N ≤ d) :
    Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) (d + 1) =
      ⨆ i : Fin (n + 1), (Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) d).map
        (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R (Fin (n + 1)) d i) :=
  Single.DegreeIdealRelations.singleDegreeIdeal_relations_succ N (Homogeneous.IdealIncidence.homogeneousDegreeRelations I N) _
    (degreeGeneratedIdeal_span_relations I N) d hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeGeneratedRelations
