import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterBaseMaps

/-! # Base Map Classifiers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.BaseMapClassifiers

noncomputable section

/-! The actual parameter base map carries every affine classifier to the classifier of the same generated quotient data over the new base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) {n B N : ℕ} {r : ℕ → ℕ} (hN : N ≤ B)

theorem generatedParameterBaseMap_classifier (R : CommRingCat.{u}) (g : Spec R ⟶ T)
    (D : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r // D.GeneratedFromDegree N}) :
    (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R g D).left ≫ ParameterBaseMaps.generatedParameterBaseMap f n B r N hN =
      (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R (g ≫ f) D).left := by
  apply (cancel_mono (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN).left).mp
  let U := D.val.quotient ⟨N, Nat.lt_succ_of_le hN⟩
  have ht : (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R g D).left ≫
      (DegreeProjection.truncatedGeneratedDegreeProjection T n B r N hN).left =
      (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R g U).left :=
    congrArg Over.Hom.left (ClassifierProjection.truncatedGeneratedClassifier_projection hN R g D)
  have hs : (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R (g ≫ f) D).left ≫
      (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN).left =
      (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R (g ≫ f) U).left :=
    congrArg Over.Hom.left (ClassifierProjection.truncatedGeneratedClassifier_projection hN R (g ≫ f) D)
  rw [Category.assoc, ParameterBaseMaps.generatedParameterBaseMap_projection, ← Category.assoc, ht, hs]
  exact Homogeneous.ParameterBaseMaps.homogeneousQuotientClassifier_postcomp f n N (r N) R g U

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.BaseMapClassifiers
