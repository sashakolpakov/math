import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PaddedWeightedMonomialGenerators
import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Graded Common Degree Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedCommonDegreeGenerators

noncomputable section

/-! A finite family of positive homogeneous generators admits a common
positive degree with finitely many homogeneous monomials controlling
all monomials whose degrees are multiples of that degree. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g]

theorem gradedExponentMonomial_mem {n : ℕ} (D : Fin n → A) (w : Fin n → ℕ)
    (hD : ∀ j, D j ∈ g (w j)) (q : Fin n → ℕ) :
    Balanced.MonomialAlgebra.exponentMonomial D q ∈ g (WeightedVeroneseExtraction.weightedExponentDegree w q) := by
  simpa only [nsmul_eq_mul, Nat.cast_id, WeightedVeroneseExtraction.weightedExponentDegree, Balanced.MonomialAlgebra.exponentMonomial] using SetLike.prod_pow_mem_graded g w D q (fun j _ => hD j)

theorem graded_common_degree_generators {n : ℕ} (D : Fin n → A) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j) (hD : ∀ j, D j ∈ g (w j)) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : Finset A,
      (∀ b ∈ B, b ∈ g N) ∧
      ∀ q : Fin n → ℕ, N ∣ WeightedVeroneseExtraction.weightedExponentDegree w q →
        Balanced.MonomialAlgebra.exponentMonomial D q ∈ Algebra.adjoin R (B : Set A) := by
  obtain ⟨N, hN, B, hB, hgen⟩ := PaddedWeightedMonomialGenerators.finite_common_degree_monomial_generators (R := R) D w hw
  have hD' (j : Fin (n + 1)) : PaddedWeightedMonomialGenerators.paddedMonomialGenerators D j ∈ g (PaddedWeightedMonomialGenerators.paddedMonomialWeights w j) := by
    refine Fin.cases ((g 1).zero_mem) hD j
  refine ⟨N, hN, B, ?_, hgen⟩
  intro b hb
  obtain ⟨q, hq, rfl⟩ := hB b hb
  exact hq ▸ gradedExponentMonomial_mem g _ _ hD' q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedCommonDegreeGenerators
