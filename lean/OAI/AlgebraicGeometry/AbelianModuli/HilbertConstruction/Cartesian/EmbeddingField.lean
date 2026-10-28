import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingFieldCriterion

/-! # Embedding Field -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.EmbeddingField

noncomputable section

/-! A field-fiber Hilbert condition can be checked on any actual Cartesian
model of the source, retaining an explicit comparison of the embedding
line bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X : Over S} {n : ℕ}
variable (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom]

theorem relativeEmbedding_fieldHilbert_cartesian_iff
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ S) (Y : Over (Spec (.of K)))
    (a : Y.left ⟶ X.left) (H : IsPullback a Y.hom X.hom x) (M : Line.Bundles.LineBundle Y.left)
    (e : (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback j.left).pullback a).sheaf ≅ M.sheaf)
    (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).homogeneousIdeal.toIdeal P ↔
      M.HasSectionHilbertPolynomial Y.hom P := by
  let O := (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback j.left
  let c := pullback.fst X.hom x
  let E : Y ≅ (Over.pullback x).obj X := Over.isoMk H.isoPullback H.isoPullback_hom_snd
  let e' : ((O.pullback c).pullback E.hom.left).sheaf ≅ M.sheaf :=
    (Scheme.Modules.pullbackComp E.hom.left c).app O.sheaf ≪≫
      (Scheme.Modules.pullbackCongr H.isoPullback_hom_fst).app O.sheaf ≪≫ e
  exact (Relative.EmbeddingFieldCriterion.relativeEmbedding_fieldHilbert_iff j x P).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso E (O.pullback c) M e' P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.EmbeddingField
