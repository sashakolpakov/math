import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ChartArbitraryPullback

/-! # Morphism Open Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismOpenFrame

noncomputable section

/-! On any open where a selected section is a frame, the global section
morphism is the normalized projective-chart map in that frame. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X : Scheme.{u}} {M : X.Modules} {n : ℕ}

theorem sectionAbsoluteMorphism_on_open_frame
    (f : X ⟶ S) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (V : X.Opens) (i : Fin (n + 1)) [IsIso (Ample.LineBundles.pullbackSection V.ι (s i))] :
    V.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs =
      ProjectiveChart.Evaluation.projectiveChartMap (V.ι ≫ f).appTop.hom
        (fun j => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection V.ι (s i)) (Ample.LineBundles.pullbackSection V.ι (s j))) i
          (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection V.ι (s i))) := by
  have hV : V ≤ Ample.LineBundles.sectionNonvanishing (s i) := le_sSup (show IsIso (Ample.LineBundles.pullbackSection V.ι (s i)) from inferInstance)
  let a := X.homOfLE hV
  have ha : a ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι = V.ι := X.homOfLE_ι hV
  calc
    _ = a ≫ ChartOverlaps.sectionAbsoluteChart f s i := by
      rw [← ha, Category.assoc, SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict]
    _ = ProjectiveChart.Evaluation.projectiveChartMap ((a ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) ≫ f).appTop.hom
        (fun j => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (a ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s i))
          (Ample.LineBundles.pullbackSection (a ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s j))) i
        (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection (a ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s i))) :=
      ChartArbitraryPullback.sectionAbsoluteChart_arbitraryPullback f s i a
    _ = _ := Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients
      (congrArg (fun k : V.toScheme ⟶ X => (k ≫ f).appTop.hom) ha)
      (funext fun j => Frame.PullbackCoherence.frameCoordinate_pullbackCongr ha (s i) (s j)) i _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismOpenFrame
