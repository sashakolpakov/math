import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingIntrinsic

/-! # Graph Twisting Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! An isomorphism of the pulled-back embedding line bundles preserves
all field-fiber Hilbert conditions, including those of a morphism graph.
The two ambient projective dimensions may differ. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

theorem GraphTwistingInvariance.relativeEmbedding_fieldHilbert_iff_of_twistingIso
    {S : Scheme.{u}} {X : Over S} {n m : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S m)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    (e : ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback i.left).sheaf ≅
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S m).pullback j.left).sheaf)
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ S) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding i).affineProjectivePullback x).homogeneousIdeal.toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).homogeneousIdeal.toIdeal P :=
  (Relative.EmbeddingFieldCriterion.relativeEmbedding_fieldHilbert_iff i x P).trans
    ((Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso (pullback.snd X.hom x) _ _
      ((Scheme.Modules.pullback (pullback.fst X.hom x)).mapIso e) P).trans
        (Relative.EmbeddingFieldCriterion.relativeEmbedding_fieldHilbert_iff j x P).symm)

theorem GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.iff_of_twistingIso
    {S : Scheme.{u}} {X Y : Over S} {n m : ℕ}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
    (i : X ⊗ Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : X ⊗ Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S m)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (e : ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback i.left).sheaf ≅
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S m).pullback j.left).sheaf)
    (P : Polynomial ℚ) (p : X ⟶ Y) :
    GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial i P p ↔ GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p := by
  let a := MorphismGraphFamilies.familyGraph p ≫ i
  let b := MorphismGraphFamilies.familyGraph p ≫ j
  let g := (MorphismGraphFamilies.familyGraph p).left
  let : IsClosedImmersion a.left := by
    change IsClosedImmersion (g ≫ i.left)
    infer_instance
  let : IsClosedImmersion b.left := by
    change IsClosedImmersion (g ≫ j.left)
    infer_instance
  let e' : ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback a.left).sheaf ≅
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S m).pullback b.left).sheaf :=
    (Scheme.Modules.pullbackComp g i.left).symm.app (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf ≪≫
      (Scheme.Modules.pullback g).mapIso e ≪≫
        (Scheme.Modules.pullbackComp g j.left).app (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S m).sheaf
  have ha : (MorphismGraphFamilies.morphismGraphFamily p).reembed i = Closed.Families.FlatClosedFamily.ofEmbedding a :=
    Closed.Families.FlatClosedFamily.ofEmbedding_reembed (MorphismGraphFamilies.familyGraph p) i
  have hb : (MorphismGraphFamilies.morphismGraphFamily p).reembed j = Closed.Families.FlatClosedFamily.ofEmbedding b :=
    Closed.Families.FlatClosedFamily.ofEmbedding_reembed (MorphismGraphFamilies.familyGraph p) j
  have H (K : Type u) [Field K] (x : Spec (.of K) ⟶ S) :
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (((MorphismGraphFamilies.morphismGraphFamily p).reembed i).affineProjectivePullback x).homogeneousIdeal.toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (((MorphismGraphFamilies.morphismGraphFamily p).reembed j).affineProjectivePullback x).homogeneousIdeal.toIdeal P := by
    rw [ha, hb]
    exact GraphTwistingInvariance.relativeEmbedding_fieldHilbert_iff_of_twistingIso a b e' x P
  exact ⟨fun hp K _ x => (H K x).mp (hp K x), fun hp K _ x => (H K x).mpr (hp K x)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
