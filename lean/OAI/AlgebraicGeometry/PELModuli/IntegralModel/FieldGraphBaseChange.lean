import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphEmbeddings
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FieldBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme

/-! # Field Graph Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGraphBaseChange

noncomputable section

/-! Actual field-coordinate embeddings commute with coefficient extension,
and the source family maps form cartesian squares. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace EndomorphismFamilies

theorem familyMap_isPullback {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {T U : Over S} (f : T ⟶ U) :
    IsPullback (EndomorphismFamiliesId.EndomorphismFamilies.familyMap A f) (pullback.snd A.scheme.hom T.hom)
      (pullback.snd A.scheme.hom U.hom) f.left :=
  IsPullback.of_iso_pullback ⟨EndomorphismFamiliesId.EndomorphismFamilies.familyMap_snd A f⟩ (EndomorphismFamiliesId.EndomorphismFamilies.schemeRestrictionIso A f).symm
    (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso_inv_fst A f) (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).inv.w

end EndomorphismFamilies

namespace PolarizationEmbedding

variable {S : Scheme.{0}} {Z : Over S}
  (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation Z)
  {k K : Type} [Field k] [Field K] (a : Spec (.of k) ⟶ S) (φ : k →+* K)

theorem e34FieldEmbedding_naturality :
    let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
    (prod.map b (𝟙 Z)).left ≫ Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B a =
      Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B (Spec.map (CommRingCat.ofHom φ) ≫ a) ≫
        AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) B.dimension := by
  let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  change (prod.map b (𝟙 Z)).left ≫ Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B a = _
  apply (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback a B.dimension).hom_ext
  · rw [Category.assoc, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_projective,
      ← Category.assoc (prod.map b (𝟙 Z)).left, ← Over.comp_left, prod.map_snd, Category.comp_id]
    rw [Category.assoc, AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_naturality, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_projective]
  · have h₁ := Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_over B a
    have h₂ := Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_over B (Spec.map (CommRingCat.ofHom φ) ≫ a)
    change ((prod.map b (𝟙 Z)).left ≫ Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B a) ≫
      HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k B.dimension =
      (Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B (Spec.map (CommRingCat.ofHom φ) ≫ a) ≫
        AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) B.dimension) ≫
          HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k B.dimension
    rw [Category.assoc, h₁, ← Over.comp_left, prod.map_fst]
    have hp : AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) B.dimension ≫
        HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k B.dimension =
      HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension ≫ Spec.map (CommRingCat.ofHom φ) :=
      AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap_over (CommRingCat.ofHom φ) B.dimension
    rw [Category.assoc, hp, ← Category.assoc, h₂]
    rfl

variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme))

theorem relativeFieldGraphEmbedding_naturality
    (r : Finite.Actions.GroupEndRing (A.pullback a)) :
    let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
    EndomorphismFamiliesId.EndomorphismFamilies.familyMap A b ≫ Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA a (r.hom (A.pullback a)) =
      Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA (Spec.map (CommRingCat.ofHom φ) ≫ a)
        ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A b r).hom _) ≫ AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) BA.dimension := by
  let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  let v := EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk a) (r.hom (A.pullback a))
  let w := EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a)) ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A b r).hom _)
  have hres : w = prod.map b (𝟙 A.scheme) ≫ v := EndomorphismHom.EndomorphismFamilies.relativeHom_restrict A b r
  have hg : (prod.map b (𝟙 A.scheme)).left ≫ (HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme v).left =
      (HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme w).left ≫ (prod.map b (𝟙 (A.scheme ⨯ A.scheme))).left := by
    have h := HilbertScheme.Presentations.HomFunctor.Hom.graph_baseChange A.scheme A.scheme b v
    rw [← hres] at h
    exact (congrArg Over.Hom.left h).symm
  apply (cancel_epi (EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a))).hom).mp
  calc
    _ = (prod.map b (𝟙 A.scheme)).left ≫ (HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme v).left ≫
        Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding BA a := by
      rw [Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding, ← Category.assoc, EndomorphismHom.EndomorphismFamilies.homSource_naturality]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rfl
    _ = (HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme w).left ≫
        (prod.map b (𝟙 (A.scheme ⨯ A.scheme))).left ≫ Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding BA a := by
      rw [← Category.assoc, hg, Category.assoc]
    _ = (HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme w).left ≫
        Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding BA (Spec.map (CommRingCat.ofHom φ) ≫ a) ≫
          AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) BA.dimension := by
      rw [e34FieldEmbedding_naturality]
    _ = _ := by
      simp only [Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding, Category.assoc, Iso.hom_inv_id_assoc]
      rfl

theorem relativeFieldGraphEmbedding_isPullback
    (r : Finite.Actions.GroupEndRing (A.pullback a)) :
    let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
    IsPullback (EndomorphismFamiliesId.EndomorphismFamilies.familyMap A b)
      (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA (Spec.map (CommRingCat.ofHom φ) ≫ a) ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A b r).hom _))
      (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA a (r.hom (A.pullback a)))
      (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) BA.dimension) := by
  let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  let e := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA a (r.hom (A.pullback a))
  let e' := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA (Spec.map (CommRingCat.ofHom φ) ≫ a) ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A b r).hom _)
  have hp : IsPullback (EndomorphismFamiliesId.EndomorphismFamilies.familyMap A b) (e' ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K BA.dimension)
      (e ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k BA.dimension) (Spec.map (CommRingCat.ofHom φ)) := by
    rw [show e' ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K BA.dimension = _ from
      Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over A BA _ _,
      show e ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap k BA.dimension = _ from
        Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over A BA _ _]
    exact EndomorphismFamilies.familyMap_isPullback A b
  exact hp.of_bot (relativeFieldGraphEmbedding_naturality a φ A BA r)
    (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (CommRingCat.ofHom φ) BA.dimension)

theorem relativeFieldGraphEmbedding_hilbertPolynomial_baseChange_iff
    (r : Finite.Actions.GroupEndRing (A.pullback a)) (P : Polynomial ℚ) :
    let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
      (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA (Spec.map (CommRingCat.ofHom φ) ≫ a)
        ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A b r).hom _)).ker).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
        (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA a (r.hom (A.pullback a))).ker).toIdeal P := by
  have hclosed := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A BA a (r.hom (A.pullback a))
  let := hclosed
  exact Projective.FieldBaseChange.PolarizationEmbedding.closedProjective_fieldBaseChange_hilbertPolynomial_iff _ _ _ φ
    (relativeFieldGraphEmbedding_isPullback a φ A BA r) P

theorem relativeIntegralGraph_hilbertPolynomial_baseChange_iff
    {O : Type} [CommRing O] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O (A.pullback a))
    (x : O) (P : Polynomial ℚ) :
    let b : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ a) ⟶ Over.mk a :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
      (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA (Spec.map (CommRingCat.ofHom φ) ≫ a)
        ((Integral.ActionScheme.restrictIntegralAction A ρ b).map x)).ker).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
        (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A BA a (ρ.map x)).ker).toIdeal P :=
  relativeFieldGraphEmbedding_hilbertPolynomial_baseChange_iff a φ A BA
    (Finite.Actions.ringHomOfIntegralAction (A.pullback a) ρ x) P

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGraphBaseChange
