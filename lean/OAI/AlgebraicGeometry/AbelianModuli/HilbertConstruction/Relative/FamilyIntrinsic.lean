import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ClosedFamilyTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.IntrinsicPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ProjectiveCriterion

/-! # Family Intrinsic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a field, the full field-fiber Hilbert condition of an actual relative projective family is exactly the intrinsic section polynomial of its relative O(1). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n))

theorem Closed.Families.FlatClosedFamily.identityAffine_intrinsicHilbertPolynomial_iff (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback (𝟙 _)).homogeneousIdeal.toIdeal P ↔
      F.relativeTwistingBundle.HasSectionHilbertPolynomial F.scheme.hom P :=
  ((F.affineProjectivePullback (𝟙 _)).homogeneousIdeal_intrinsicHilbertPolynomial_iff P).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso F.identityAffineFamilyIso F.relativeTwistingBundle
      (F.affineProjectivePullback (𝟙 _)).twistingBundle F.identityAffineTwistingBundleIso P).symm

theorem Closed.Families.FlatClosedFamily.fieldHilbert_intrinsic_iff (P : Polynomial ℚ) :
    (∀ (L : Type u) [Field L] (x : Spec (.of L) ⟶ Spec (.of K)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal.toIdeal P) ↔
      F.relativeTwistingBundle.HasSectionHilbertPolynomial F.scheme.hom P :=
  (F.fieldHilbert_iff_identity P).trans (F.identityAffine_intrinsicHilbertPolynomial_iff P)

theorem Closed.Families.FlatClosedFamily.relativeTwistingBundle_hilbertPolynomial_exists :
    ∃ P : Polynomial ℚ, F.relativeTwistingBundle.HasSectionHilbertPolynomial F.scheme.hom P := by
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (F.affineProjectivePullback (𝟙 _)).homogeneousIdeal
  exact ⟨P, (F.identityAffine_intrinsicHilbertPolynomial_iff P).mp hP⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
