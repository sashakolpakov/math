import OAI.AlgebraicGeometry.PELModuli.CMPoints.GraphFiberCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FieldBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point

/-! # Graph Field Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.GraphFieldHilbertPolynomial

noncomputable section

/-! A graph over a field has the same Hilbert polynomial after every
field-valued base change. The coordinates are those of its actual closed
immersion, and the comparison squares are proved cartesian. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FieldBaseChange.PolarizationEmbedding
universe u

theorem categorical_product_baseChange {S : Scheme.{u}} (X : Over S)
    {T U : Over S} (b : T ⟶ U) :
    IsPullback (prod.map b (𝟙 X)).left (prod.fst : T ⨯ X ⟶ T).left
      (prod.fst : U ⨯ X ⟶ U).left b.left := by
  have hU : IsPullback (prod.snd : U ⨯ X ⟶ X).left
      (prod.fst : U ⨯ X ⟶ U).left X.hom U.hom :=
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd U X)).flip
  have hT : IsPullback ((prod.map b (𝟙 X)).left ≫ (prod.snd : U ⨯ X ⟶ X).left)
      (prod.fst : T ⨯ X ⟶ T).left X.hom (b.left ≫ U.hom) := by
    have hs : (prod.map b (𝟙 X)).left ≫ (prod.snd : U ⨯ X ⟶ X).left =
        (prod.snd : T ⨯ X ⟶ X).left := by
      simpa only [Over.comp_left, Category.comp_id] using
        congrArg Over.Hom.left (prod.map_snd b (𝟙 X))
    rw [hs, b.w]
    exact (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T X)).flip
  exact hT.of_right (congrArg Over.Hom.left (prod.map_fst b (𝟙 X))) hU

theorem graphFamily_hasFiberHilbertPolynomial_of_field_coordinates
    {S : Scheme.{u}} (X Y : Over S)
    [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsSeparated Y.hom] {k : Type u} [Field k]
    (t : Spec (.of k) ⟶ S) (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ Y))
    (f : Over.mk t ⨯ X ⟶ Y) (P : Polynomial ℚ)
    (q : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k B.dimension) ⟶ HilbertScheme.Presentations.Has.Core.projectiveSpace S B.dimension)
    (j : (Over.mk t ⨯ X).left ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k B.dimension))
    (hq : IsPullback q (HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k B.dimension)
      (HilbertScheme.Presentations.Has.Core.projectiveSpaceProjection S B.dimension) t)
    [IsClosedImmersion j]
    (hjq : j ≫ q = (HilbertScheme.Presentations.HomFunctor.Hom.graph X Y f).left ≫
      (prod.snd : Over.mk t ⨯ (X ⨯ Y) ⟶ X ⨯ Y).left ≫ B.embedding)
    (hjp : j ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k B.dimension =
      (prod.fst : Over.mk t ⨯ X ⟶ Over.mk t).left)
    (hP : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf j.ker).toIdeal P) :
    HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial B (HilbertScheme.Presentations.HomFunctor.Hom.graphFamily X Y f) P := by
  apply GraphFiberCoordinates.graphFamily_hasFiberHilbertPolynomial_of_coordinates X Y B f P
  intro K _ a
  let T : Over S := Over.mk t
  let U : Over S := Over.mk (a ≫ t)
  let b : U ⟶ T := Over.homMk a rfl
  let c := (prod.map b (𝟙 X)).left
  let φ : k →+* K := (Spec.preimage a).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = a := Spec.map_preimage a
  let := φ.toAlgebra
  let pK := HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension
  let p := HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k B.dimension
  let v := AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) B.dimension
  have hp : IsPullback v pK p a := by
    rw [← hφ]
    exact AbelianModuli.HilbertConstruction.Projective.CoefficientPullback.polynomialProjectiveCoefficient_isPullback
  have hc : (c ≫ j) ≫ p = (prod.fst : U ⨯ X ⟶ U).left ≫ a := by
    rw [Category.assoc, hjp]
    exact congrArg Over.Hom.left (prod.map_fst b (𝟙 X))
  let e := hp.lift (c ≫ j) (prod.fst : U ⨯ X ⟶ U).left hc
  have hev : e ≫ v = c ≫ j := hp.lift_fst _ _ hc
  have hep : e ≫ pK = (prod.fst : U ⨯ X ⟶ U).left := hp.lift_snd _ _ hc
  have hepb : IsPullback c e j v := by
    have ho : IsPullback c (e ≫ pK) (j ≫ p) a := by
      rw [hep, hjp]
      exact categorical_product_baseChange X b
    exact ho.of_bot hev.symm hp
  have he : IsClosedImmersion e :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hepb inferInstance
  refine ⟨v ≫ q, e, hp.paste_horiz hq, he, ?_, hep, ?_⟩
  · have heq : e ≫ (v ≫ q) = c ≫ (j ≫ q) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun d => d ≫ q) hev).trans (Category.assoc _ _ _))
    have hg : prod.map b (𝟙 X) ≫ HilbertScheme.Presentations.HomFunctor.Hom.graph X Y f ≫ prod.snd =
        HilbertScheme.Presentations.HomFunctor.Hom.graph X Y (prod.map b (𝟙 X) ≫ f) ≫ prod.snd := by
      apply prod.hom_ext <;>
        simp only [HilbertScheme.Presentations.HomFunctor.Hom.graph, Category.assoc, prod.lift_snd, prod.lift_fst,
          prod.map_snd, Category.comp_id]
    exact heq.trans ((congrArg (fun d => c ≫ d) hjq).trans
      ((Category.assoc _ _ _).symm.trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun d => d.left ≫ B.embedding) hg))))
  · have hj : IsClosedImmersion j := inferInstance
    exact (@IntegralModel.Projective.FieldBaseChange.PolarizationEmbedding.closedProjective_fieldBaseChange_hilbertPolynomial_iff
      k K _ _ B.dimension _ _ j hj e c φ hepb P).mpr hP

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.GraphFieldHilbertPolynomial
