import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FamilyIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery

/-! # Embedding Intrinsic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingIntrinsic

noncomputable section

/-! The full Hilbert condition of an actual relative projective embedding, including an embedded morphism graph, is the intrinsic polynomial of its pulled-back O(1). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {n : ℕ} {A : Over (Spec (.of K))}
variable (i : A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
variable [IsClosedImmersion i.left] [Flat A.hom] [LocallyOfFinitePresentation A.hom]

def relativeEmbeddingTwistingBundleIso :
    ((Closed.Families.FlatClosedFamily.ofEmbedding i).relativeTwistingBundle.pullback (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).hom.left).sheaf ≅
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback i.left).sheaf := by
  have he : (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).hom.left ≫ (Closed.Families.FlatClosedFamily.ofEmbedding i).inclusion.left =
      i.left := congrArg Over.Hom.left (Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion i)
  exact (Scheme.Modules.pullbackComp (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).hom.left
      (Closed.Families.FlatClosedFamily.ofEmbedding i).inclusion.left).app (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).sheaf ≪≫
    (Scheme.Modules.pullbackCongr he).app (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).sheaf

theorem relativeEmbedding_hilbertPolynomial_iff (P : Polynomial ℚ) :
    (∀ (L : Type u) [Field L] (x : Spec (.of L) ⟶ Spec (.of K)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding i).affineProjectivePullback x).homogeneousIdeal.toIdeal P) ↔
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback i.left).HasSectionHilbertPolynomial A.hom P :=
  ((Closed.Families.FlatClosedFamily.ofEmbedding i).fieldHilbert_intrinsic_iff P).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso (Closed.Families.FlatClosedFamily.ofEmbeddingIso i)
      (Closed.Families.FlatClosedFamily.ofEmbedding i).relativeTwistingBundle
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback i.left)
      (relativeEmbeddingTwistingBundleIso i) P)

theorem relativeEmbedding_intrinsicHilbertPolynomial_exists :
    ∃ P : Polynomial ℚ,
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback i.left).HasSectionHilbertPolynomial A.hom P := by
  obtain ⟨P, hP⟩ := (Closed.Families.FlatClosedFamily.ofEmbedding i).relativeTwistingBundle_hilbertPolynomial_exists
  exact ⟨P, (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso (Closed.Families.FlatClosedFamily.ofEmbeddingIso i)
    (Closed.Families.FlatClosedFamily.ofEmbedding i).relativeTwistingBundle
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback i.left)
    (relativeEmbeddingTwistingBundleIso i) P).mp hP⟩

open _root_.CategoryTheory.MonoidalCategory

theorem embeddedGraph_intrinsicHilbertPolynomial_iff
    {B : Over (Spec (.of K))} [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (p : A ⟶ B) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p ↔
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) n).pullback (MorphismGraphFamilies.familyGraph p ≫ j).left).HasSectionHilbertPolynomial A.hom P := by
  have : IsClosedImmersion (MorphismGraphFamilies.familyGraph p ≫ j).left :=
    inferInstanceAs (IsClosedImmersion ((MorphismGraphFamilies.familyGraph p).left ≫ j.left))
  have he := Closed.Families.FlatClosedFamily.ofEmbedding_reembed (MorphismGraphFamilies.familyGraph p) j
  have hpoly := congrArg (fun F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n) =>
    ∀ (L : Type u) [Field L] (x : Spec (.of L) ⟶ Spec (.of K)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal.toIdeal P) he
  exact hpoly.to_iff.trans (relativeEmbedding_hilbertPolynomial_iff (MorphismGraphFamilies.familyGraph p ≫ j) P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingIntrinsic
