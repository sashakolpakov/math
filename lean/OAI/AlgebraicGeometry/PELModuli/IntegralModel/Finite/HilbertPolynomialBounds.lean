import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialTest
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis
import Mathlib.Data.Set.Finite.Range
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Hilbert Polynomial Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.HilbertPolynomialBounds.PolarizationEmbedding

noncomputable section

/-! Bounded homogeneous equations admit only finitely many Hilbert
polynomials, uniformly over all coefficient fields. The finite set is
obtained from actual quotient dimensions and polynomial interpolation. -/

open _root_.MvPolynomial

theorem finite_polynomials_of_bounded_values (n b : ℕ) (C : Fin (n + 1) → ℕ) :
    Set.Finite {P : Polynomial ℚ | P.natDegree ≤ n ∧
      ∀ i : Fin (n + 1), ∃ v : ℕ, v ≤ C i ∧ P.eval ((b + i.val : ℕ) : ℚ) = v} := by
  classical
  let ev (P : Polynomial ℚ) (i : Fin (n + 1)) := P.eval ((b + i.val : ℕ) : ℚ)
  let encode (v : ∀ i : Fin (n + 1), Fin (C i + 1)) (i : Fin (n + 1)) : ℚ := (v i).val
  apply Set.Finite.of_injOn (f := ev) (t := Set.range encode)
  · intro P hP
    choose v hv he using hP.2
    refine ⟨fun i => ⟨v i, Nat.lt_succ_of_le (hv i)⟩, ?_⟩
    exact funext (fun i => (he i).symm)
  · intro P hP Q hQ h
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q
      (f := fun i : Fin (n + 1) => ((b + i.val : ℕ) : ℚ))
    · intro i j hij
      change ((b + i.val : ℕ) : ℚ) = ((b + j.val : ℕ) : ℚ) at hij
      have he : b + i.val = b + j.val := by exact_mod_cast hij
      exact Fin.ext (Nat.add_left_cancel he)
    · exact fun i => congrFun h i
    · rw [Fintype.card_fin]
      exact Nat.lt_succ_of_le (max_le hP.1 hQ.1)
  · exact Set.finite_range encode

universe u

theorem hilbertFunction_le_degreeMonomials {K : Type u} [Field K] {n : ℕ}
    (I : Ideal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction I d ≤ Nat.card (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n d) := by
  change Module.finrank K ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n d) ⧸ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I d) ≤ _
  exact (Submodule.finrank_quotient_le (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I d)).trans_eq
    (Module.finrank_eq_nat_card_basis (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.degreeMonomialBasis K n d))

theorem exists_finite_hilbertPolynomials_of_bounded_generators (n D : ℕ) :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (K : Type u) [Field K] (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n))
        (B : Finset (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)),
        I.toIdeal = Ideal.span (B : Set (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) →
        (∀ f ∈ B, f ≠ 0 ∧ ∃ d ≤ D, f.IsHomogeneous d) →
        ∀ P : Polynomial ℚ, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P → P ∈ F := by
  classical
  let b := HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D
  let C (i : Fin (n + 1)) := Nat.card (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n (b + i.val))
  let hF := finite_polynomials_of_bounded_values n b C
  refine ⟨hF.toFinset, fun K _ I B hB hdeg P hP => ?_⟩
  apply hF.mem_toFinset.mpr
  have hp := (HilbertScheme.Presentations.Finite.PolynomialTest.GradedHilbert.bounded_generators_hilbertPolynomial_finite_test I B hB D hdeg P).mp hP
  refine ⟨hp.1, fun i => ⟨HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (b + i.val), ?_, (hp.2 i).symm⟩⟩
  exact hilbertFunction_le_degreeMonomials I.toIdeal (b + i.val)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.HilbertPolynomialBounds.PolarizationEmbedding
