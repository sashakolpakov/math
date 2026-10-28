import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ConjugateLabels
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic

/-! # Labels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.Labels.Construction

noncomputable section

/-!
Specialize conjugate-pair indexing to the actual rational Galois group of
the CM field. Its cardinality is derived from the Galois degree, and the
second half is literal complex conjugation of the chosen first half.
-/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [IsGalois ℚ E]

omit [IsGalois ℚ E] in
theorem cmConjugation_involutive :
    Function.Involutive (fun τ : Gal(E/ℚ) => PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) := by
  have hc : PELModuli.CMPoints.Arithmetic.rationalConjugation E * PELModuli.CMPoints.Arithmetic.rationalConjugation E = 1 := by
    ext x
    exact NumberField.IsCMField.complexConj_apply_apply E x
  intro τ
  change PELModuli.CMPoints.Arithmetic.rationalConjugation E * (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) = τ
  rw [← mul_assoc, hc, one_mul]

def cmConjugateLabels (s : ℕ) (hdegree : Module.finrank ℚ E = 2 * s)
    (chosen : Set Gal(E/ℚ))
    (hchosen : ∀ τ, τ ∈ chosen ↔ PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ ∉ chosen) :
    (Fin s ⊕ Fin s) ≃ Gal(E/ℚ) :=
  ConjugateLabels.Construction.indexedConjugateLabels (Equiv.mulLeft (PELModuli.CMPoints.Arithmetic.rationalConjugation E))
    cmConjugation_involutive chosen hchosen s (by
      rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hdegree])

theorem cmConjugateLabels_opposite (s : ℕ) (hdegree : Module.finrank ℚ E = 2 * s)
    (chosen : Set Gal(E/ℚ))
    (hchosen : ∀ τ, τ ∈ chosen ↔ PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ ∉ chosen)
    (i : Fin s) :
    cmConjugateLabels s hdegree chosen hchosen (Sum.inr i) =
      PELModuli.CMPoints.Arithmetic.rationalConjugation E * cmConjugateLabels s hdegree chosen hchosen (Sum.inl i) := rfl

theorem cmConjugateLabels_chosen (s : ℕ) (hdegree : Module.finrank ℚ E = 2 * s)
    (chosen : Set Gal(E/ℚ))
    (hchosen : ∀ τ, τ ∈ chosen ↔ PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ ∉ chosen)
    (i : Fin s) : cmConjugateLabels s hdegree chosen hchosen (Sum.inl i) ∈ chosen := by
  classical
  exact Subtype.property _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.Labels.Construction
