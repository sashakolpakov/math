import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

/-! # Projective Target Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTargetIso

noncomputable section

/-! Changing the sheaf presentation of a line bundle preserves the
projective morphism defined by its transported sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} {M Q : X.Modules} {n : ℕ}

theorem sectionProjectiveMorphism_congr (f : X ⟶ S)
    {s t : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M)} (h : s = t)
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i)) :
    SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs = SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht := by
  subst t
  rfl

theorem sections_compIso_covers (e : M ≅ Q)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i ≫ e.hom) := by
  intro x
  obtain ⟨i, hi⟩ := hs x
  exact ⟨i, (Ample.Powers.sectionNonvanishing_comp_iso (s i) e).symm ▸ hi⟩

theorem sectionAbsoluteMorphism_targetIso (f : X ⟶ S) (e : M ≅ Q)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i ≫ e.hom)) :
    SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism f (fun i => s i ≫ e.hom) ht := by
  apply (SectionsProjectiveMorphism.sectionOpenCover s hs).hom_ext
  intro i
  change Fin (n + 1) at i
  let U := Ample.LineBundles.sectionNonvanishing (s i)
  let V := Ample.LineBundles.sectionNonvanishing (s i ≫ e.hom)
  have hUV : U = V := (Ample.Powers.sectionNonvanishing_comp_iso (s i) e).symm
  let a : U.toScheme ⟶ V.toScheme := (X.isoOfEq hUV).hom
  have ha : a ≫ V.ι = U.ι := X.isoOfEq_hom_ι hUV
  let : IsIso (Ample.LineBundles.pullbackSection U.ι (s i ≫ e.hom)) := by
    rw [Power.SectionTransitions.pullbackSection_postcomp]
    infer_instance
  calc
    U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs = ChartOverlaps.sectionAbsoluteChart f s i :=
      SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs i
    _ = a ≫ ChartOverlaps.sectionAbsoluteChart f (fun k => s k ≫ e.hom) i := by
      symm
      refine (ChartArbitraryPullback.sectionAbsoluteChart_arbitraryPullback f (fun k => s k ≫ e.hom) i a).trans ?_
      apply Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients
      · exact congrArg (fun q => (q ≫ f).appTop.hom) ha
      · funext k
        exact (Frame.PullbackCoherence.frameCoordinate_pullbackCongr ha (s i ≫ e.hom) (s k ≫ e.hom)).trans
          ((Power.SectionTransitions.frameCoordinate_pullback_postcomp U.ι (s i) (s i ≫ e.hom) e.hom rfl (s k)).trans
            (Frame.Coordinates.sectionRatio_eq_frameCoordinate (s i) (s k)).symm)
    _ = U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f (fun k => s k ≫ e.hom) ht := by
      rw [← SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f (fun k => s k ≫ e.hom) ht i,
        ← Category.assoc, ha]

theorem sectionProjectiveMorphism_targetIso (f : X ⟶ S) (e : M ≅ Q)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i ≫ e.hom)) :
    SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs =
      SectionsProjectiveMorphism.sectionProjectiveMorphism f (fun i => s i ≫ e.hom) ht := by
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · rw [ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection, ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection]
    exact sectionAbsoluteMorphism_targetIso f e s hs ht
  · rw [SectionsProjectiveMorphism.sectionProjectiveMorphism_over, SectionsProjectiveMorphism.sectionProjectiveMorphism_over]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTargetIso
