import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ChartArbitraryPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps

/-! # Projective Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveBaseChange

noncomputable section

/-! The projective morphism defined by a generating family of line-bundle
sections commutes with base change, with its actual Cartesian square. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S T X Y : Scheme.{u}} {n : ℕ}

theorem sectionAbsoluteMorphism_postcomp_base (p : X ⟶ T) (b : T ⟶ S)
    {M : X.Modules} (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    SectionsProjectiveMorphism.sectionAbsoluteMorphism p s hs ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap b.appTop n =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism (p ≫ b) s hs := by
  apply (SectionsProjectiveMorphism.sectionOpenCover s hs).hom_ext
  intro i
  change ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism p s hs) ≫
      Projective.CoefficientFunctoriality.polynomialProjectiveMap b.appTop n =
    (Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism (p ≫ b) s hs
  rw [SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict, SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict]
  exact ProjectiveChart.CoefficientNaturality.projectiveChartMap_coefficientMap b.appTop.hom
    ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ p).appTop.hom
    (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i))

theorem sectionProjectiveMorphism_coefficientProjection (p : X ⟶ S)
    {M : X.Modules} (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left ≫ RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism p s hs := pullback.lift_fst _ _ _

theorem sectionProjectiveMorphism_baseChange (a : Y ⟶ X) (b : T ⟶ S)
    (p : X ⟶ S) (q : Y ⟶ T) (w : a ≫ p = q ≫ b) (L : Line.Bundles.LineBundle X)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ y : Y, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection a (s i))) :
    a ≫ (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left =
      (SectionsProjectiveMorphism.sectionProjectiveMorphism q (fun i => Ample.LineBundles.pullbackSection a (s i)) ht).left ≫
        RelativeProjective.BaseMaps.relativeProjectiveBaseMap b n := by
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · rw [Category.assoc, sectionProjectiveMorphism_coefficientProjection,
      Category.assoc, RelativeProjective.BaseMaps.relativeProjectiveBaseMap_fst, ← Category.assoc,
      sectionProjectiveMorphism_coefficientProjection,
      sectionAbsoluteMorphism_postcomp_base,
      ChartArbitraryPullback.sectionAbsoluteMorphism_pullback_source p a L s hs ht]
    exact congrArg (fun f => SectionsProjectiveMorphism.sectionAbsoluteMorphism f
      (fun i => Ample.LineBundles.pullbackSection a (s i)) ht) w
  · rw [Category.assoc, SectionsProjectiveMorphism.sectionProjectiveMorphism_over, Category.assoc,
      RelativeProjective.BaseMaps.relativeProjectiveBaseMap_over, ← Category.assoc, SectionsProjectiveMorphism.sectionProjectiveMorphism_over]
    exact w

theorem sectionProjectiveMorphism_isPullback (a : Y ⟶ X) (b : T ⟶ S)
    (p : X ⟶ S) (q : Y ⟶ T) (H : IsPullback a q p b) (L : Line.Bundles.LineBundle X)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ y : Y, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection a (s i))) :
    IsPullback a (SectionsProjectiveMorphism.sectionProjectiveMorphism q (fun i => Ample.LineBundles.pullbackSection a (s i)) ht).left
      (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap b n) := by
  have h : IsPullback a
      ((SectionsProjectiveMorphism.sectionProjectiveMorphism q (fun i => Ample.LineBundles.pullbackSection a (s i)) ht).left ≫
        (Projective.ProjectivePresentations.projectiveSpaceOver T n).hom)
      ((SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom) b := by
    rw [SectionsProjectiveMorphism.sectionProjectiveMorphism_over, SectionsProjectiveMorphism.sectionProjectiveMorphism_over]
    exact H
  exact h.of_bot (sectionProjectiveMorphism_baseChange a b p q H.w L s hs ht)
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback b n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveBaseChange
