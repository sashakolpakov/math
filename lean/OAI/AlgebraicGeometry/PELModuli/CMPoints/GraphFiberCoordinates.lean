import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert

/-! # Graph Fiber Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.GraphFiberCoordinates

noncomputable section

/-! Owned adaptation of the Presentations graph-coordinate helper with the projective
presentation qualified to avoid the category-theoretic namesake.

Construct Presentations's field-fiber coordinates from coordinates on the actual
source of a graph. The image subscheme and its defining ideal are compared
through the closed graph's canonical image isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S)
  [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]

theorem graphFamily_hasFiberHilbertPolynomial_of_coordinates
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ Y)) {T : Over S}
    (f : T ⨯ X ⟶ Y) (P : Polynomial ℚ)
    (h : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ T.left),
      let t : Over S := Over.mk (a ≫ T.hom)
      let b : t ⟶ T := Over.homMk a rfl
      let v := prod.map b (𝟙 X) ≫ f
      ∃ (q : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K B.dimension) ⟶ HilbertScheme.Presentations.Has.Core.projectiveSpace S B.dimension)
        (e : (t ⨯ X).left ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K B.dimension)),
        IsPullback q (HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension)
          (HilbertScheme.Presentations.Has.Core.projectiveSpaceProjection S B.dimension) (a ≫ T.hom) ∧
        IsClosedImmersion e ∧
        e ≫ q = (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left ≫ (prod.snd : t ⨯ (X ⨯ Y) ⟶ X ⨯ Y).left ≫ B.embedding ∧
        e ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension = (prod.fst : t ⨯ X ⟶ t).left ∧
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker).toIdeal P) :
    HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial B (HilbertScheme.Presentations.HomFunctor.Hom.graphFamily X Y f) P := by
  intro K _ a
  let t : Over S := Over.mk (a ≫ T.hom)
  let b : t ⟶ T := Over.homMk a rfl
  let v := prod.map b (𝟙 X) ≫ f
  obtain ⟨q, e, hq, he, heq, hep, hP⟩ := h K a
  have hg : IsClosedImmersion (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left := HilbertScheme.Presentations.HomFunctor.Hom.graph_isClosedImmersion X Y v
  let := hg
  let c := (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left.toImage
  have hi : IsIso c := inferInstance
  let := hi
  let ci := asIso c
  change ∃ q e, _
  change ∃ (q : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K B.dimension) ⟶ HilbertScheme.Presentations.Has.Core.projectiveSpace S B.dimension)
    (e : (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (X ⨯ Y) b (HilbertScheme.Presentations.HomFunctor.Hom.graphFamily X Y f)).val.subscheme ⟶
      Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K B.dimension)), _
  rw [← HilbertScheme.Presentations.HomFunctor.Hom.graphFamily_baseChange X Y b f]
  dsimp only [HilbertScheme.Presentations.HomFunctor.Hom.graphFamily, HilbertScheme.Presentations.HomFunctor.Hom.graphIdeal, HilbertScheme.Presentations.Hilbert.Functor.familyProjection]
  refine ⟨q, ci.inv ≫ e, hq, ?_, ?_, ?_, ?_⟩
  · let := he
    infer_instance
  · rw [Category.assoc, heq]
    have hci : ci.hom ≫ (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left.imageι = (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left :=
      (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left.toImage_imageι
    have hi : ci.inv ≫ (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left = (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y v).left.imageι := by
      apply (cancel_epi ci.hom).mp
      exact (ci.hom_inv_id_assoc _).trans hci.symm
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun d => d ≫ (prod.snd : t ⨯ (X ⨯ Y) ⟶ X ⨯ Y).left ≫ B.embedding) hi)
  · apply (cancel_epi ci.hom).mp
    rw [Category.assoc, ci.hom_inv_id_assoc, hep]
    exact (HilbertScheme.Presentations.HomFunctor.Hom.graph_image_projection X Y v).symm
  · rw [Scheme.Hom.ker_comp_of_isIso]
    exact hP

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.GraphFiberCoordinates
