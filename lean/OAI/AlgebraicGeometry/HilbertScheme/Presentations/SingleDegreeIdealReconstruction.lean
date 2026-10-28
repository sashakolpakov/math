import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal

/-! # Single Degree Ideal Reconstruction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeIdealReconstruction.GradedHilbert

noncomputable section

/-! Ideals generated in one degree are recovered from exactly that
relation degree, including normalized polynomial Grassmannian ideals. -/

universe u v
variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type v} [Fintype ι]

omit [Fintype ι] in
theorem degreeGeneratedIdeal_of_generators (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ)
    (hg : ∀ i, (g i).IsHomogeneous N) :
    DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) N = Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg := by
  apply HomogeneousIdeal.ext
  apply le_antisymm (DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_le _ N)
  apply Ideal.span_le.mpr
  rintro f ⟨i, rfl⟩
  exact DegreeGeneratedIdeal.GradedHilbert.mem_degreeGeneratedIdeal _ N (g i) (hg i) (Ideal.subset_span (Set.mem_range_self i))

variable {κ : Type u} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem normalizedPolynomialIdeal_eq_degreeGenerated
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ) (a : κ → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix κ (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R)
    (h : Hilbert.Polynomial.GradedHilbert.degreeRelations (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal N = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N) :
    Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N := by
  have he := DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal_eq_of_degreeRelations_eq (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q) I N h
  exact (degreeGeneratedIdeal_of_generators (Normalized.PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a Q) N
    (Normalized.PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator_homogeneous a Q)).symm.trans he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeIdealReconstruction.GradedHilbert
