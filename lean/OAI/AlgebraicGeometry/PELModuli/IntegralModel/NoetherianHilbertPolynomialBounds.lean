import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.HilbertPolynomialBounds
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import Mathlib.RingTheory.Polynomial.Basic

/-! # Noetherian Hilbert Polynomial Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianHilbertPolynomialBounds.PolarizationEmbedding

noncomputable section

/-! A fixed homogeneous ideal over a noetherian coefficient ring has
only finitely many Hilbert polynomials after specialization to any field. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_finite_field_specialization_hilbertPolynomials
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (K : Type v) [Field K] (φ : R →+* K) (P : Polynomial ℚ),
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal P → P ∈ F := by
  classical
  obtain ⟨B, hB, hhom⟩ := HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules.noetherian_homogeneous_generators
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) I.toIdeal I.isHomogeneous
  let d (f : B) : ℕ := (hhom f.val f.property).choose
  have hd (f : B) : f.val.IsHomogeneous (d f) := (hhom f.val f.property).choose_spec
  let D : ℕ := Finset.univ.sup d
  obtain ⟨F, hF⟩ := Finite.HilbertPolynomialBounds.PolarizationEmbedding.exists_finite_hilbertPolynomials_of_bounded_generators.{v} n D
  refine ⟨F, fun K _ φ P hP => ?_⟩
  let C := (B.image (MvPolynomial.map φ)).erase 0
  have hspan : (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal =
      Ideal.span (C : Set (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
    change Ideal.map (MvPolynomial.map φ) I.toIdeal = _
    rw [← hB, Ideal.map_span]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro f ⟨g, hg, rfl⟩
      by_cases hz : MvPolynomial.map φ g = 0
      · simpa only [hz, SetLike.mem_coe] using
          (Ideal.zero_mem (Ideal.span (C : Set (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))))
      · exact Ideal.subset_span (Finset.mem_erase.mpr
          ⟨hz, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩)
    · apply Ideal.span_le.mpr
      intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hf).2
      exact Ideal.subset_span ⟨g, hg, rfl⟩
  apply hF K (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) C hspan _ P hP
  intro f hf
  have hf0 := (Finset.mem_erase.mp hf).1
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hf).2
  refine ⟨hf0, d ⟨g, hg⟩, ?_, (hd ⟨g, hg⟩).map φ⟩
  exact Finset.le_sup (f := d) (Finset.mem_univ (⟨g, hg⟩ : B))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianHilbertPolynomialBounds.PolarizationEmbedding
