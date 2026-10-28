import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackEmbeddingTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.IntrinsicPolynomial

/-! # Embedding Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingFieldCriterion

noncomputable section

/-! The Hilbert condition on every field-valued point of an arbitrary base
is the intrinsic polynomial of the actual pulled-back embedding line bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X : Over S} {n : ℕ}
variable (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom]

theorem relativeEmbedding_fieldHilbert_iff
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ S) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).homogeneousIdeal.toIdeal P ↔
      (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback j.left).pullback (pullback.fst X.hom x)).HasSectionHilbertPolynomial (pullback.snd X.hom x) P :=
  (((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).homogeneousIdeal_intrinsicHilbertPolynomial_iff P).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso (Affine.PullbackEmbeddingTwisting.affinePullbackEmbeddingIso j x)
      ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).twistingBundle
      (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback j.left).pullback (pullback.fst X.hom x))
      (Affine.PullbackEmbeddingTwisting.affinePullbackEmbeddingTwistingIso j x) P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingFieldCriterion
