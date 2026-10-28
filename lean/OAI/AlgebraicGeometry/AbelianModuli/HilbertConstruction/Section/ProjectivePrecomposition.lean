import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveBaseChange

/-! # Projective Precomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePrecomposition

noncomputable section

/-! A morphism over the base pulls a generating section family back to
the family defining the composite projective morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem sectionProjectiveMorphism_precomp {S : Scheme.{u}} {X Y : Over S} (a : X ⟶ Y)
    (L : Line.Bundles.LineBundle Y.left) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule Y.left ⟶ L.sheaf))
    (hs : ∀ y : Y.left, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection a.left (s i))) :
    a ≫ SectionsProjectiveMorphism.sectionProjectiveMorphism Y.hom s hs =
      SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom (fun i => Ample.LineBundles.pullbackSection a.left (s i)) ht := by
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · change (a.left ≫ (SectionsProjectiveMorphism.sectionProjectiveMorphism Y.hom s hs).left) ≫ _ = _
    rw [Category.assoc, ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection,
      ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection,
      ChartArbitraryPullback.sectionAbsoluteMorphism_pullback_source Y.hom a.left L s hs ht]
    exact congrArg (fun p => SectionsProjectiveMorphism.sectionAbsoluteMorphism p (fun i => Ample.LineBundles.pullbackSection a.left (s i)) ht) a.w
  · exact (a ≫ SectionsProjectiveMorphism.sectionProjectiveMorphism Y.hom s hs).w.trans
      (SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom _ ht).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePrecomposition
