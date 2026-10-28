import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianHilbertPolynomialBounds

/-! # Uniform Fiber Hilbert Function -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformFiberHilbertFunction.PolarizationEmbedding

noncomputable section

/-! One degree bound controls the Hilbert functions of every field
specialization of a fixed noetherian homogeneous ideal. -/

open _root_.MvPolynomial

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_uniform_field_specialization_hilbertFunction
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    ∃ b : ℕ, ∀ (K : Type v) [Field K] (φ : R →+* K) (P : Polynomial ℚ),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal P →
      ∀ d ≥ b, (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal d : ℚ) =
        P.eval (d : ℚ) := by
  classical
  obtain ⟨B, hB, hhom⟩ := HilbertScheme.Presentations.Graded.ModuleGenerators.GradedModules.noetherian_homogeneous_generators
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) I.toIdeal I.isHomogeneous
  let e (f : B) : ℕ := (hhom f.val f.property).choose
  have he (f : B) : f.val.IsHomogeneous (e f) := (hhom f.val f.property).choose_spec
  let D : ℕ := Finset.univ.sup e
  refine ⟨HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D, fun K _ φ P hP d hd => ?_⟩
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
  apply HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.bounded_generators_hilbertFunction_eq (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) C hspan D _ P hP d hd
  intro f hf
  have hf0 := (Finset.mem_erase.mp hf).1
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hf).2
  exact ⟨hf0, e ⟨g, hg⟩, Finset.le_sup (f := e) (Finset.mem_univ (⟨g, hg⟩ : B)),
    (he ⟨g, hg⟩).map φ⟩

theorem hilbertPolynomial_iff_uniform_values
    {R : Type u} [CommRing R] {n b : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : ∀ (K : Type v) [Field K] (φ : R →+* K) (P : Polynomial ℚ),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal P →
      ∀ d ≥ b, (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal d : ℚ) =
        P.eval (d : ℚ))
    {K : Type v} [Field K] (φ : R →+* K) (P : Polynomial ℚ) (a : ℕ) (ha : b ≤ a) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal P ↔
      P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal (a + i.val) : ℚ) =
          P.eval ((a + i.val : ℕ) : ℚ) := by
  constructor
  · intro hP
    exact ⟨HilbertScheme.Presentations.Finite.PolynomialTest.GradedHilbert.hilbertPolynomial_natDegree_le _ P hP,
      fun i => hI K φ P hP _ (ha.trans (Nat.le_add_right _ _))⟩
  · rintro ⟨hdeg, hvals⟩
    obtain ⟨Q, hQ⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))
    have heq : Q = P := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq Q P
        (f := fun i : Fin (n + 1) => ((a + i.val : ℕ) : ℚ))
      · intro i j hij
        change ((a + i.val : ℕ) : ℚ) = ((a + j.val : ℕ) : ℚ) at hij
        have he : a + i.val = a + j.val := by exact_mod_cast hij
        exact Fin.ext (Nat.add_left_cancel he)
      · intro i
        exact (hI K φ Q hQ _ (ha.trans (Nat.le_add_right _ _))).symm.trans (hvals i)
      · rw [Fintype.card_fin]
        exact Nat.lt_succ_of_le (max_le (HilbertScheme.Presentations.Finite.PolynomialTest.GradedHilbert.hilbertPolynomial_natDegree_le _ Q hQ) hdeg)
    exact heq ▸ hQ

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformFiberHilbertFunction.PolarizationEmbedding
