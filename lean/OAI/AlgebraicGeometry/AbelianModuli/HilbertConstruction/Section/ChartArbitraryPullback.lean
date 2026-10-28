import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

/-! # Chart Arbitrary Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ChartArbitraryPullback

noncomputable section

/-! Section charts commute with arbitrary source morphisms. The comparison
uses the actual pulled-back sections and their nonvanishing opens. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false

variable {S X Y : Scheme.{u}} {n : ℕ}

theorem sectionRatio_arbitraryPullback {M : X.Modules}
    (s t : Line.Bundles.structureModule X ⟶ M) (h : Y ⟶ (Ample.LineBundles.sectionNonvanishing s).toScheme) :
    h.appTop (Frames.sectionRatio s t) = Frame.Coordinates.frameCoordinate
      (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing s).ι) s)
      (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing s).ι) t) := by
  exact (congrArg (fun a => h.appTop a) (Frame.Coordinates.sectionRatio_eq_frameCoordinate s t)).trans
    ((Scalar.BaseChange.frameCoordinate_baseChange h (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s)
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t)).symm.trans
        (Frame.PullbackCoherence.frameCoordinate_pullbackComp (Ample.LineBundles.sectionNonvanishing s).ι h s t).symm)

theorem sectionAbsoluteChart_arbitraryPullback (f : X ⟶ S) {M : X.Modules}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M)) (i : Fin (n + 1))
    (h : Y ⟶ (Ample.LineBundles.sectionNonvanishing (s i)).toScheme) :
    h ≫ ChartOverlaps.sectionAbsoluteChart f s i =
      ProjectiveChart.Evaluation.projectiveChartMap ((h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) ≫ f).appTop.hom
        (fun k => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s i))
          (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s k))) i
        (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s i))) := by
  exact (ProjectiveChart.Naturality.projectiveChartMap_comp h ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
    (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i))).trans
      (Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients (by rfl)
        (funext fun k => sectionRatio_arbitraryPullback (s i) (s k) h) i _ _)

def lineBundleNonvanishingBaseMap (h : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection h s)).toScheme ⟶ (Ample.LineBundles.sectionNonvanishing s).toScheme :=
  h.resLE (Ample.LineBundles.sectionNonvanishing s) (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection h s))
    (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange h L s).le

theorem lineBundleNonvanishingBaseMap_ι (h : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    lineBundleNonvanishingBaseMap h L s ≫ (Ample.LineBundles.sectionNonvanishing s).ι =
      (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection h s)).ι ≫ h :=
  Scheme.Hom.resLE_comp_ι h (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange h L s).le

theorem lineBundleSections_pullback_covers (h : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    ∀ y : Y, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection h (s i)) := by
  intro y
  obtain ⟨i, hi⟩ := hs (h y)
  refine ⟨i, ?_⟩
  rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange]
  exact hi

theorem sectionAbsoluteMorphism_pullback_source (f : X ⟶ S) (h : Y ⟶ X)
    (L : Line.Bundles.LineBundle X) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ht : ∀ y : Y, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection h (s i))) :
    h ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism (h ≫ f) (fun i => Ample.LineBundles.pullbackSection h (s i)) ht := by
  apply (SectionsProjectiveMorphism.sectionOpenCover (fun i => Ample.LineBundles.pullbackSection h (s i)) ht).hom_ext
  intro i
  let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection h (s i))
  let a := lineBundleNonvanishingBaseMap h L (s i)
  have ha : a ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι = V.ι ≫ h :=
    lineBundleNonvanishingBaseMap_ι h L (s i)
  let : IsIso (Ample.LineBundles.pullbackSection (V.ι ≫ h) (s i)) :=
    (Nonvanishing.isIso_pullbackSection_comp_iff h V.ι (s i)).mp inferInstance
  calc
    V.ι ≫ (h ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) = a ≫ ChartOverlaps.sectionAbsoluteChart f s i := by
      rw [← Category.assoc, ← ha, Category.assoc, SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict]
    _ = ChartOverlaps.sectionAbsoluteChart (h ≫ f) (fun k => Ample.LineBundles.pullbackSection h (s k)) i := by
      rw [sectionAbsoluteChart_arbitraryPullback]
      apply Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients
      · exact congrArg (fun q => q.appTop.hom)
          ((congrArg (fun q => q ≫ f) ha).trans (Category.assoc _ _ _))
      · funext k
        exact (Frame.PullbackCoherence.frameCoordinate_pullbackCongr ha (s i) (s k)).trans
          ((Frame.PullbackCoherence.frameCoordinate_pullbackComp h V.ι (s i) (s k)).trans
            (Frame.Coordinates.sectionRatio_eq_frameCoordinate _ _).symm)
    _ = V.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism (h ≫ f) (fun k => Ample.LineBundles.pullbackSection h (s k)) ht :=
      (SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict _ _ _ i).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ChartArbitraryPullback
