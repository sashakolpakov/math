import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.DegreeGenerators

/-! # Single Degree Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite multiplication-surjectivity conditions force the generated ideal to be generated in one retained degree. -/

universe u v

section

variable {R : Type u} [CommRing R] {σ : Type v} (E : GradedIdealReconstruction.GradedIdealRelations R σ)

theorem GradedIdealReconstruction.GradedIdealRelations.lowDegreeRelations_eq_last (N : ℕ) (hzero : ∀ d < N, E.piece d = ⊥) :
    E.lowDegreeRelations N = (E.piece N).map (MvPolynomial.homogeneousSubmodule σ R N).subtype := by
  apply le_antisymm
  · apply iSup_le
    intro d
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ d.isLt) with hd | hd
    · rw [hzero d hd, Submodule.map_bot]
      exact bot_le
    · rw [hd]
  · exact le_iSup (fun d : Fin (N + 1) =>
      (E.piece d).map (MvPolynomial.homogeneousSubmodule σ R d).subtype) ⟨N, Nat.lt_succ_self N⟩

end

namespace Truncated

variable {R : Type u} [CommRing R] {σ : Type v} {B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R σ B r) (N : ℕ)

def GradedClassification.TruncatedGradedQuotientData.GeneratedFromDegree : Prop :=
  (∀ d : Fin (B + 1), d.val < N → (D.quotient d).toSubmodule = ⊥) ∧
  ∀ d : Fin B, N ≤ d.val → (D.quotient d.succ).toSubmodule =
    ⨆ i : σ, ((D.quotient d.castSucc).toSubmodule).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)

theorem GradedClassification.TruncatedGradedQuotientData.extensionPiece_generatedFrom (h : D.GeneratedFromDegree N) (d : ℕ) (hd : N ≤ d) :
    D.extensionPiece (d + 1) =
      ⨆ i : σ, (D.extensionPiece d).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i) := by
  by_cases hb : d < B
  · rw [D.extensionPiece_retained (d + 1) (by omega), D.extensionPiece_retained d (by omega)]
    exact h.2 ⟨d, hb⟩ hd
  · exact D.extensionPiece_generated d (by omega)

theorem GradedClassification.TruncatedGradedQuotientData.generatedIdeal_span_degree (hN : N ≤ B) (h : D.GeneratedFromDegree N) :
    D.generatedIdeal.toIdeal = Ideal.span
      (((D.quotient ⟨N, Nat.lt_succ_of_le hN⟩).toSubmodule).map
        (MvPolynomial.homogeneousSubmodule σ R N).subtype : Set (MvPolynomial σ R)) := by
  have hzero : ∀ d < N, D.generatedRelations.piece d = ⊥ := by
    intro d hd
    change D.extensionPiece d = ⊥
    rw [D.extensionPiece_retained d (by omega)]
    exact h.1 ⟨d, by omega⟩ hd
  have hgen : D.generatedRelations.lowDegreeIdeal N = D.generatedIdeal.toIdeal :=
    D.generatedRelations.lowDegreeIdeal_eq N (D.extensionPiece_generatedFrom N h)
  rw [← hgen]
  change Ideal.span (D.generatedRelations.lowDegreeRelations N : Set (MvPolynomial σ R)) = _
  rw [D.generatedRelations.lowDegreeRelations_eq_last N hzero]
  change Ideal.span ((D.extensionPiece N).map
    (MvPolynomial.homogeneousSubmodule σ R N).subtype : Set (MvPolynomial σ R)) = _
  rw [D.extensionPiece_retained N hN]

theorem GradedClassification.TruncatedGradedQuotientData.generatedIdeal_span_generators (hN : N ≤ B) (h : D.GeneratedFromDegree N) :
    D.generatedIdeal.toIdeal = Ideal.span
      (Set.range (fun i => (D.degreeGenerators ⟨N, Nat.lt_succ_of_le hN⟩ i).val)) := by
  rw [D.generatedIdeal_span_degree N hN h, ← D.degreeGenerators_span]
  rw [Submodule.map_span, ← Set.range_comp]
  exact Submodule.span_span_of_tower R (MvPolynomial σ R) _

end Truncated

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
