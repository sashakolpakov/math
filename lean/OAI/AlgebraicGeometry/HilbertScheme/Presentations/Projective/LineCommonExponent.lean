import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineExponentSymmetry

/-! # Line Common Exponent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineCommonExponent

noncomputable section

/-! Every line bundle on projective space over a field has one integer
exponent for all standard-chart transitions, including projective dimension one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem symmetric_triple_value_constant {α : Type u} {β : Type v}
    (e : (i j : α) → j ≠ i → β)
    (hsym : ∀ i j hji, e i j hji = e j i hji.symm)
    (htri : ∀ i j k hji hkj hki, e i j hji = e j k hkj ∧ e j k hkj = e i k hki)
    (a b : α) (hba : b ≠ a) : ∀ i j hji, e i j hji = e a b hba := by
  classical
  have hrow (j : α) (hja : j ≠ a) : e a j hja = e a b hba := by
    by_cases hjb : j = b
    · subst j
      rfl
    · exact ((htri a b j hba hjb hja).1.trans (htri a b j hba hjb hja).2).symm
  intro i j hji
  by_cases hia : i = a
  · subst i
    exact hrow j hji
  by_cases hja : j = a
  · subst j
    exact (hsym i a hji).trans (hrow i hia)
  exact (htri a i j hia hji hja).1.symm.trans (hrow i hia)

variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

def projectiveLineCommonExponent : ℤ :=
  if hn : 0 < n then
    FrameExponents.projectiveLineTransitionExponent K 0 ⟨1, Nat.succ_lt_succ hn⟩ (by simp) L
  else 0

theorem projectiveLineTransitionExponent_eq_common (i j : Fin (n + 1)) (hji : j ≠ i) :
    FrameExponents.projectiveLineTransitionExponent K i j hji L = projectiveLineCommonExponent K L := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    exact hji (Fin.ext (by have hi := i.isLt; have hj := j.isLt; omega))
  rw [projectiveLineCommonExponent, dite_eq_left hn]
  exact symmetric_triple_value_constant (fun i j hji => FrameExponents.projectiveLineTransitionExponent K i j hji L)
    (LineExponentSymmetry.projectiveLineTransitionExponent_symm K L) (LineRationalCocycle.projectiveLineTransitionExponent_triple K L)
    0 ⟨1, Nat.succ_lt_succ hn⟩ (by simp) i j hji

theorem projectiveLineTransitionValue_common_monomial (i j : Fin (n + 1)) (hji : j ≠ i) :
    ∃ c : Kˣ, OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue K L i j) =
      RationalTransitionExponentComparison.rationalProjectiveMonomial c i j (projectiveLineCommonExponent K L) := by
  obtain ⟨c, hc⟩ := OverlapRationalMonomials.projectiveOverlapFunctionFieldMap_unit K i j hji (LineTransitionPowers.projectiveLineTransitionUnit K L i j)
  refine ⟨c, ?_⟩
  have hc' : OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue K L i j) =
      RationalTransitionExponentComparison.rationalProjectiveMonomial c i j (FrameExponents.projectiveLineTransitionExponent K i j hji L) := by
    simpa only [FrameExponents.projectiveLineTransitionExponent, LineTransitionPowers.projectiveLineTransitionUnit, IsUnit.unit_spec] using hc
  rwa [projectiveLineTransitionExponent_eq_common] at hc'

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineCommonExponent
