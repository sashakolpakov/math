import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMonomialCompletion

/-! # Support Monomial Completion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.SupportMonomialCompletion

noncomputable section

/-! The completing balanced monomial can be chosen with a positive
exponent on every originally nonzero maximal minor. -/
open scoped Classical
universe u
variable {K : Type u} [Field K] {r m : ℕ}

theorem sparseConfiguration_complete_with_positive_support
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m)
    (b : (Fin r → Fin m) → ℕ) (hb : Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b ≠ 0) :
    ∃ a C : (Fin r → Fin m) → ℕ,
      a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight ∧ C + b = a ∧
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a ≠ 0 ∧
      ∀ τ, LabeledDeterminantPolynomials.labeledDeterminant τ v ≠ 0 → 0 < a τ := by
  let d : (Fin r → Fin m) → ℕ := fun τ => if LabeledDeterminantPolynomials.labeledDeterminant τ v ≠ 0 then 1 else 0
  have hd : Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) d ≠ 0 := by
    apply (NonvanishingMonomialCompletion.exponentMonomial_ne_zero_iff _ d).mpr
    intro τ hτ hz
    have hdτ : d τ = 0 := ite_eq_right (fun hn => hn hz)
    exact hτ hdτ
  have hbd : Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (b + d) ≠ 0 := by
    rw [Balanced.MonomialAlgebra.exponentMonomial_add]
    exact mul_ne_zero hb hd
  obtain ⟨a, C, ha, he, han⟩ := NonvanishingMonomialCompletion.sparseConfiguration_complete_nonvanishing_monomial v hv hr hm hs (b + d) hbd
  refine ⟨a, C + d, ha, ?_, han, ?_⟩
  · calc
      C + d + b = C + (b + d) := by ac_rfl
      _ = a := he
  · intro τ hτ
    have hdτ : d τ = 1 := ite_eq_left hτ
    have h := congrFun he τ
    change C τ + (b τ + d τ) = a τ at h
    omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.SupportMonomialCompletion
