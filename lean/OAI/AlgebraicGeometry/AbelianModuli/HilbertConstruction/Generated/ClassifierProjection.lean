import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeProjection

/-! # Classifier Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ClassifierProjection

noncomputable section

/-! The generating-degree projection of a classified tuple is the classifier of its generating quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ} (hN : N ≤ B)

theorem truncatedGeneratedClassifier_projection (R : CommRingCat.{u}) (f : Spec R ⟶ S)
    (D : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r // D.GeneratedFromDegree N}) :
    Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN =
      Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f
        (D.val.quotient ⟨N, Nat.lt_succ_of_le hN⟩) := by
  change Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D ≫
    (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N ≫
      Truncated.GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S ⟨N, Nat.lt_succ_of_le hN⟩) = _
  rw [← Category.assoc, Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv_inclusion,
    Truncated.GradedClassification.TruncatedGradedQuotientData.classifyingMap_projection]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ClassifierProjection
