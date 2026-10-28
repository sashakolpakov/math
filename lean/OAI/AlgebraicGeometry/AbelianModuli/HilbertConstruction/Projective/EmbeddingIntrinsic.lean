import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.IntrinsicPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.EmbeddingIso

/-! # Embedding Intrinsic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Hilbert polynomial of the actual ideal family of any closed projective embedding is the intrinsic section polynomial of the pulled-back ambient O(1). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {A : Over (Spec (.of R))}
variable (j : A ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n)
variable [IsClosedImmersion j.left] [Flat A.hom] [LocallyOfFinitePresentation A.hom]

def Projective.EmbeddingIntrinsic.projectiveEmbeddingTwistingBundleIso :
    ((Closed.Families.FlatClosedFamily.ofEmbedding j).twistingBundle.pullback (Closed.Families.FlatClosedFamily.ofEmbeddingIso j).hom.left).sheaf ≅
      ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback j.left).sheaf := by
  have he : (Closed.Families.FlatClosedFamily.ofEmbeddingIso j).hom.left ≫ (Closed.Families.FlatClosedFamily.ofEmbedding j).inclusion.left =
      j.left := congrArg Over.Hom.left (Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion j)
  exact (Scheme.Modules.pullbackComp (Closed.Families.FlatClosedFamily.ofEmbeddingIso j).hom.left
      (Closed.Families.FlatClosedFamily.ofEmbedding j).inclusion.left).app (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf ≪≫
    (Scheme.Modules.pullbackCongr he).app (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf

theorem Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso
    {K : Type u} [Field K] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    (L M : Line.Bundles.LineBundle Y) (e : L.sheaf ≅ M.sheaf) (P : Polynomial ℚ) :
    L.HasSectionHilbertPolynomial p P ↔ M.HasSectionHilbertPolynomial p P :=
  Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sectionIso p p L M P
    (fun d => Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso p ((TensorPower.Maps.tensorPowerFunctor Y d).mapIso e))

variable {K : Type u} [Field K] {B : Over (Spec (.of K))}
variable (i : B ⟶ Projective.ProjectivePresentations.affineProjectiveSpace K n)
variable [IsClosedImmersion i.left] [Flat B.hom] [LocallyOfFinitePresentation B.hom]

theorem Projective.EmbeddingIntrinsic.projectiveEmbedding_hilbertPolynomial_iff (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Closed.Families.FlatClosedFamily.ofEmbedding i).homogeneousIdeal.toIdeal P ↔
      ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle K n).pullback i.left).HasSectionHilbertPolynomial B.hom P :=
  ((Closed.Families.FlatClosedFamily.ofEmbedding i).homogeneousIdeal_intrinsicHilbertPolynomial_iff P).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_overIso (Closed.Families.FlatClosedFamily.ofEmbeddingIso i)
      (Closed.Families.FlatClosedFamily.ofEmbedding i).twistingBundle ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle K n).pullback i.left)
      (Projective.EmbeddingIntrinsic.projectiveEmbeddingTwistingBundleIso i) P)

theorem Projective.EmbeddingIntrinsic.projectiveEmbedding_hilbertPolynomial_iff_of_bundleIso (L : Line.Bundles.LineBundle B.left)
    (e : ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle K n).pullback i.left).sheaf ≅ L.sheaf) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Closed.Families.FlatClosedFamily.ofEmbedding i).homogeneousIdeal.toIdeal P ↔
      L.HasSectionHilbertPolynomial B.hom P :=
  (Projective.EmbeddingIntrinsic.projectiveEmbedding_hilbertPolynomial_iff i P).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso B.hom
      ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle K n).pullback i.left) L e P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
