import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.WeightedDegreeMonomials
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.GeneratorMonomialPresentation

/-! # Padded Weighted Monomial Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PaddedWeightedMonomialGenerators

noncomputable section

/-! A zero generator of weight one makes the generator list nonempty
without changing its monomials. A common positive degree then has a
finite list of monomials generating every divisible-degree monomial. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def paddedMonomialGenerators {n : ℕ} (D : Fin n → A) : Fin (n + 1) → A := Fin.cons 0 D
def paddedMonomialWeights {n : ℕ} (w : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cons 1 w

theorem paddedMonomialGenerators_monomial {n : ℕ} (D : Fin n → A) (q : Fin n → ℕ) :
    Balanced.MonomialAlgebra.exponentMonomial (paddedMonomialGenerators D) (Fin.cons 0 q) = Balanced.MonomialAlgebra.exponentMonomial D q := by
  simp only [Balanced.MonomialAlgebra.exponentMonomial, paddedMonomialGenerators, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, pow_zero, one_mul]

theorem paddedMonomialWeights_degree {n : ℕ} (w : Fin n → ℕ) (q : Fin n → ℕ) :
    WeightedVeroneseExtraction.weightedExponentDegree (paddedMonomialWeights w) (Fin.cons 0 q) = WeightedVeroneseExtraction.weightedExponentDegree w q := by
  simp only [WeightedVeroneseExtraction.weightedExponentDegree, paddedMonomialWeights, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]

theorem finite_common_degree_monomial_generators {n : ℕ} (D : Fin n → A)
    (w : Fin n → ℕ) (hw : ∀ j, 0 < w j) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : Finset A,
      (∀ b ∈ B, ∃ q : Fin (n + 1) → ℕ,
        WeightedVeroneseExtraction.weightedExponentDegree (paddedMonomialWeights w) q = N ∧
          Balanced.MonomialAlgebra.exponentMonomial (paddedMonomialGenerators D) q = b) ∧
      ∀ q : Fin n → ℕ, N ∣ WeightedVeroneseExtraction.weightedExponentDegree w q →
        Balanced.MonomialAlgebra.exponentMonomial D q ∈ Algebra.adjoin R (B : Set A) := by
  let w' := paddedMonomialWeights w
  have hw' (j : Fin (n + 1)) : 0 < w' j := by
    refine Fin.cases (by exact Nat.zero_lt_one) hw j
  let L := ∏ j, w' j
  have hL : 0 < L := Finset.prod_pos (fun j _ => hw' j)
  have hwL (j : Fin (n + 1)) : w' j ∣ L := Finset.dvd_prod_of_mem w' (Finset.mem_univ j)
  obtain ⟨B, hB, hgen⟩ := Finite.WeightedDegreeMonomials.weightedVeronese_finite_degree_generators (R := R) (Nat.succ_pos n)
    w' hw' L hL hwL (paddedMonomialGenerators D)
  refine ⟨(n + 1) * L, Nat.mul_pos (Nat.succ_pos n) hL, B, hB, ?_⟩
  intro q hq
  rw [hgen]
  apply Algebra.subset_adjoin
  refine ⟨Fin.cons 0 q, ?_, paddedMonomialGenerators_monomial D q⟩
  change (n + 1) * L ∣ WeightedVeroneseExtraction.weightedExponentDegree (paddedMonomialWeights w) (Fin.cons 0 q)
  rw [paddedMonomialWeights_degree]
  exact hq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PaddedWeightedMonomialGenerators
