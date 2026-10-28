import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.BalancedExponentGenerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialFiniteSums
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMonomialCompletion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantAlgebra

/-! # Generator Monomial Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.GeneratorMonomialPresentation

noncomputable section

/-! Natural combinations of balanced generators preserve both their
weighted degree and their actual determinant monomial. -/
open scoped BigOperators Classical
universe u v w
variable {κ : Type u} [Fintype κ] {ι : Type v}

theorem monomialMultiDegree_generator_sum {n : ℕ} (w : κ → ι → ℕ)
    (B : Fin n → κ → ℕ) (q : Fin n → ℕ) (i : ι) :
    ExponentFiniteGeneration.monomialMultiDegree w (∑ j, q j • B j) i = ∑ j, q j * ExponentFiniteGeneration.monomialMultiDegree w (B j) i := by
  simp only [MonomialFiniteSums.monomialMultiDegree_sum, ExponentCompletion.monomialMultiDegree_nsmul]

theorem exponentMonomial_generator_sum {A : Type w} [CommRing A] {n : ℕ}
    (D : κ → A) (B : Fin n → κ → ℕ) (q : Fin n → ℕ) :
    MonomialAlgebra.exponentMonomial D (∑ j, q j • B j) = MonomialAlgebra.exponentMonomial (fun j => MonomialAlgebra.exponentMonomial D (B j)) q := by
  simp only [MonomialFiniteSums.exponentMonomial_sum, NonvanishingMonomialCompletion.exponentMonomial_nsmul]
  rfl

theorem balancedDeterminant_positive_degree_generators {r m : ℕ} (hr : 0 < r) (i : Fin m) :
    ∃ (n : ℕ) (B : Fin n → (Fin r → Fin m) → ℕ),
      (∀ j, B j ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight ∧
        0 < ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (B j) i) ∧
      ∀ a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight,
        ∃ q : Fin n → ℕ, a = ∑ j, q j • B j := by
  obtain ⟨n, B, hB, hrep⟩ := Positive.BalancedExponentGenerators.balancedExponentMonoid_positive_generator_representation
    (DeterminantBlockDegrees.labeledDeterminantWeight (r := r) (m := m))
  refine ⟨n, B, fun j => ⟨(hB j).1, ?_⟩, hrep⟩
  exact Nat.pos_of_ne_zero (fun hz => (hB j).2
    ((DeterminantAlgebra.balancedDeterminantMonomial_degree_zero_iff hr (B j) (hB j).1 i).mp hz))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.GeneratorMonomialPresentation
