import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialTest

/-! # Generated Polynomial Test -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedPolynomialTest.GradedHilbert

noncomputable section

/-! The finite Hilbert-polynomial test for a homogeneous generating family, allowing zero equations after specialization. -/

open _root_.MvPolynomial

universe u z

variable {K : Type u} [Field K] {n : ℕ} {ι : Type z} [Fintype ι]

theorem homogeneousGenerators_hilbertPolynomial_finite_test
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal P ↔
      P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal
          (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val) : ℚ) =
          P.eval ((Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ) := by
  classical
  let B := (Finset.univ.image g).erase 0
  have hB : (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      by_cases hi : g i = 0
      · simpa only [hi, SetLike.mem_coe] using (Ideal.zero_mem (Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))))
      · exact Ideal.subset_span (Finset.mem_erase.mpr ⟨hi, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    · apply Ideal.span_le.mpr
      intro f hf
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hf).2
      exact Ideal.subset_span (Set.mem_range_self i)
  apply Finite.PolynomialTest.GradedHilbert.bounded_generators_hilbertPolynomial_finite_test _ B hB N _ P
  intro f hf
  obtain ⟨hf0, hfg⟩ := Finset.mem_erase.mp hf
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hfg
  exact ⟨hf0, N, le_rfl, hg i⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedPolynomialTest.GradedHilbert
