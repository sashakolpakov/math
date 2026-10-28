import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphHilbertBaseChange

/-! # Field Pullback Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Hilbert-polynomial bound on an embedded graph depends only on all field-valued pullbacks of its underlying morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem Graph.FieldPullbackEquality.embeddedGraph_affinePullback_eq_of_map_eq
    {S : Scheme.{u}} {A B : Over S} {n : ℕ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (f q : A ⟶ B) {R : CommRingCat.{u}} (s : Spec R ⟶ S)
    (h : (Over.pullback s).map f = (Over.pullback s).map q) :
    ((MorphismGraphFamilies.morphismGraphFamily f).reembed j).affineProjectivePullback s =
      ((MorphismGraphFamilies.morphismGraphFamily q).reembed j).affineProjectivePullback s := by
  have he : ((MorphismGraphFamilies.morphismGraphFamily f).reembed j).projectiveBaseChange s =
      ((MorphismGraphFamilies.morphismGraphFamily q).reembed j).projectiveBaseChange s := by
    rw [Embedded.GraphBaseChange.embeddedMorphismGraphFamily_projectiveBaseChange, Embedded.GraphBaseChange.embeddedMorphismGraphFamily_projectiveBaseChange, h]
  have H := congrArg (fun F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec R) n) =>
    F.affineProjectivePullback (𝟙 _)) he
  simpa only [Closed.Families.FlatClosedFamily.projectiveBaseChange_affine, Category.id_comp] using H

theorem Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.of_fieldPullback_eq
    {S : Scheme.{u}} {A B : Over S} {n : ℕ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)
    {f q : A ⟶ B} (hf : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map q) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P q := by
  intro K _ s
  have he := Graph.FieldPullbackEquality.embeddedGraph_affinePullback_eq_of_map_eq j f q s (h K s)
  exact (congrArg (fun F => HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Closed.Families.FlatClosedFamily.homogeneousIdeal F).toIdeal P) he).mp (hf K s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
