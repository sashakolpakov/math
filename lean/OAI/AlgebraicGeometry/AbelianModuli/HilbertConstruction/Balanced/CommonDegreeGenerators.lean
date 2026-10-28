import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedCommonDegreeGenerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameCoordinatePolynomials

/-! # Common Degree Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.CommonDegreeGenerators

noncomputable section

/-! The balanced determinant algebra has a finite common-degree family
controlling every balanced monomial in a multiple of that degree. -/
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] {r m : ℕ}

theorem balancedDeterminant_common_degree_generators (hr : 0 < r) (i : Fin m) :
    ∃ N : ℕ, 0 < N ∧ ∃ F : Finset (DeterminantAlgebra.balancedDeterminantAlgebra R r m),
      (∀ x ∈ F, x ∈ DeterminantGrading.balancedDeterminantGrading R r m i N) ∧
      ∀ a (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight),
        N ∣ ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i →
          FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha ∈ Algebra.adjoin R (F : Set (DeterminantAlgebra.balancedDeterminantAlgebra R r m)) := by
  obtain ⟨n, B, hB, hrep⟩ := GeneratorMonomialPresentation.balancedDeterminant_positive_degree_generators hr i
  let D := fun j : Fin n => FrameCoordinatePolynomials.balancedDeterminantMonomialElement R (B j) (hB j).1
  let w := fun j : Fin n => ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (B j) i
  obtain ⟨N, hN, F, hF, hgen⟩ := GradedCommonDegreeGenerators.graded_common_degree_generators
    (DeterminantGrading.balancedDeterminantGrading R r m i) D w (fun j => (hB j).2)
    (fun j => FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R (B j) (hB j).1 i)
  refine ⟨N, hN, F, hF, ?_⟩
  intro a ha hdiv
  obtain ⟨q, hq⟩ := hrep a ha
  have hwq : WeightedVeroneseExtraction.weightedExponentDegree w q = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i := by
    rw [hq, GeneratorMonomialPresentation.monomialMultiDegree_generator_sum]
    rfl
  have hDq : MonomialAlgebra.exponentMonomial D q = FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha := by
    apply Subtype.ext
    change (DeterminantAlgebra.balancedDeterminantAlgebra R r m).val.toRingHom (MonomialAlgebra.exponentMonomial D q) =
      MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a
    rw [MonomialExponentExtension.exponentMonomial_map]
    change MonomialAlgebra.exponentMonomial (fun j => MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (B j)) q = _
    rw [← GeneratorMonomialPresentation.exponentMonomial_generator_sum, ← hq]
  rw [← hDq]
  exact hgen q (hwq.symm ▸ hdiv)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.CommonDegreeGenerators
