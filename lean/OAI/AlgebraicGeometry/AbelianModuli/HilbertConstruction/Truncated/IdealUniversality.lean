import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.IdealExtension

/-! # Ideal Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-!
The reconstructed finite-data ideal is the least homogeneous ideal containing
the retained relations. This is an actual ideal-generation universal property.
-/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} {B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R σ B r)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GradedClassification.TruncatedGradedQuotientData.generatedIdeal_le_iff (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    D.generatedIdeal.toIdeal ≤ J.toIdeal ↔
      ∀ d : Fin (B + 1), (D.quotient d).toSubmodule ≤ Homogeneous.IdealIncidence.homogeneousDegreeRelations J d := by
  constructor
  · intro h d p hp
    have hd : p ∈ Homogeneous.IdealIncidence.homogeneousDegreeRelations D.generatedIdeal d :=
      (D.generatedIdeal_degree d).symm ▸ hp
    exact h hd
  · intro h
    rw [← D.generatedIdeal_generated]
    apply Ideal.span_le.mpr
    change D.generatedRelations.lowDegreeRelations B ≤ J.toIdeal.restrictScalars R
    apply iSup_le
    intro d
    rintro _ ⟨p, hp, rfl⟩
    change p ∈ D.extensionPiece d at hp
    rw [D.extensionPiece_retained d (Nat.le_of_lt_succ d.isLt)] at hp
    exact h d hp

theorem GradedClassification.TruncatedGradedQuotientData.generatedIdeal_unique
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (hJ : (GradedIdealReconstruction.homogeneousIdealRelations J).lowDegreeIdeal B = J.toIdeal)
    (h : ∀ d : Fin (B + 1), Homogeneous.IdealIncidence.homogeneousDegreeRelations J d = (D.quotient d).toSubmodule) :
    D.generatedIdeal = J := by
  apply HomogeneousIdeal.ext
  apply le_antisymm
  · exact (D.generatedIdeal_le_iff J).mpr (fun d => (h d).ge)
  · rw [← hJ]
    apply Ideal.span_le.mpr
    change (GradedIdealReconstruction.homogeneousIdealRelations J).lowDegreeRelations B ≤
      D.generatedIdeal.toIdeal.restrictScalars R
    apply iSup_le
    intro d
    rintro _ ⟨p, hp, rfl⟩
    change p ∈ Homogeneous.IdealIncidence.homogeneousDegreeRelations J d at hp
    rw [h d] at hp
    change p ∈ Homogeneous.IdealIncidence.homogeneousDegreeRelations D.generatedIdeal d
    rw [D.generatedIdeal_degree]
    exact hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
