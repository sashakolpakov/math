import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.TwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IntrinsicPolynomial

/-! # Intrinsic Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual flat closed projective family over a field has the same homogeneous Hilbert polynomial as the intrinsic section polynomial of its restricted ambient O(1). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace K n))

theorem Closed.Families.FlatClosedFamily.homogeneousIdeal_intrinsicHilbertPolynomial_iff (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial F.homogeneousIdeal.toIdeal P ↔
      F.twistingBundle.HasSectionHilbertPolynomial F.scheme.hom P :=
  (Projective.IntrinsicPolynomial.projectiveTwistingBundle_intrinsicHilbertPolynomial_iff F.homogeneousIdeal P).symm.trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso F.homogeneousFamilyIso F.twistingBundle
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle F.homogeneousIdeal 1) F.homogeneousTwistingBundleIso P).symm

theorem Closed.Families.FlatClosedFamily.twistingBundle_hilbertPolynomial_exists :
    ∃ P : Polynomial ℚ, F.twistingBundle.HasSectionHilbertPolynomial F.scheme.hom P := by
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial F.homogeneousIdeal
  exact ⟨P, (F.homogeneousIdeal_intrinsicHilbertPolynomial_iff P).mp hP⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
