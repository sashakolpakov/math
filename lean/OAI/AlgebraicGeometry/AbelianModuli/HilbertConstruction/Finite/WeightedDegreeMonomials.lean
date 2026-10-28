import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.WeightedVeroneseGeneration

/-! # Weighted Degree Monomials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.WeightedDegreeMonomials

noncomputable section

/-! Positive weights leave only finitely many monomials in a prescribed
degree. The explicit Veronese algebra thus has finite degree-one generators. -/
open scoped BigOperators Classical
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

theorem finite_weightedExponentDegree_fiber {n : ℕ} (w : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) : {a : Fin n → ℕ | WeightedVeroneseExtraction.weightedExponentDegree w a = N}.Finite := by
  let B := {a : Fin n → ℕ | WeightedVeroneseExtraction.weightedExponentDegree w a = N}
  have hbound (a : B) (i : Fin n) : a.val i ≤ N := by
    have hterm : a.val i * w i ≤ WeightedVeroneseExtraction.weightedExponentDegree w a.val :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (a.val j * w j)) (Finset.mem_univ _)
    have hpos : a.val i ≤ a.val i * w i := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a.val i) (Nat.succ_le_of_lt (hw i))
    exact hpos.trans (hterm.trans_eq a.property)
  let f : B → (Fin n → Fin (N + 1)) := fun a i => ⟨a.val i, Nat.lt_succ_of_le (hbound a i)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hab i)
  let : Finite B := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp inferInstance

theorem finite_weightedDegreeMonomials {n : ℕ} (w : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (D : Fin n → A) (N : ℕ) :
    (Balanced.MonomialAlgebra.exponentMonomial D '' {a | WeightedVeroneseExtraction.weightedExponentDegree w a = N}).Finite :=
  (finite_weightedExponentDegree_fiber w hw N).image _

theorem weightedVeronese_finite_degree_generators {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (L : ℕ) (hL : 0 < L)
    (hwL : ∀ i, w i ∣ L) (D : Fin n → A) :
    ∃ B : Finset A,
      (∀ b ∈ B, ∃ a : Fin n → ℕ, WeightedVeroneseExtraction.weightedExponentDegree w a = n * L ∧ Balanced.MonomialAlgebra.exponentMonomial D a = b) ∧
      Algebra.adjoin R (B : Set A) =
        Algebra.adjoin R (Balanced.MonomialAlgebra.exponentMonomial D '' {a | n * L ∣ WeightedVeroneseExtraction.weightedExponentDegree w a}) := by
  let hB := finite_weightedDegreeMonomials w hw D (n * L)
  refine ⟨hB.toFinset, ?_, ?_⟩
  · intro b hb
    exact hB.mem_toFinset.mp hb
  · rw [hB.coe_toFinset, WeightedVeroneseGeneration.weightedVeronese_adjoin_eq_degree_adjoin hn w hw L hL hwL D]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.WeightedDegreeMonomials
