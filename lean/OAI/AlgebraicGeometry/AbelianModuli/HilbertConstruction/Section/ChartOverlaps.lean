import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.ProjectiveMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality

/-! # Chart Overlaps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ChartOverlaps

noncomputable section

/-! Section-defined projective-chart maps agree on the actual scheme-theoretic overlaps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y : Scheme.{u}} {L : X.Modules} {n : ℕ}

/-- The chart map to projective space over the global functions of the base. -/
def sectionAbsoluteChart (f : X ⟶ S) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (i : Fin (n + 1)) : (Ample.LineBundles.sectionNonvanishing (s i)).toScheme ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
  ProjectiveChart.Evaluation.projectiveChartMap ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
    (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i))

/-- Restrict a section chart by pulling all its sections directly to the smaller scheme. -/
theorem sectionAbsoluteChart_restrict (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i : Fin (n + 1))
    (h : Y ⟶ (Ample.LineBundles.sectionNonvanishing (s i)).toScheme) [IsOpenImmersion h] :
    h ≫ sectionAbsoluteChart f s i =
      ProjectiveChart.Evaluation.projectiveChartMap ((h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) ≫ f).appTop.hom
        (fun k => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s i))
          (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s k))) i
        (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection (h ≫ (Ample.LineBundles.sectionNonvanishing (s i)).ι) (s i))) := by
  exact (ProjectiveChart.Naturality.projectiveChartMap_comp h ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
    (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i))).trans
      (Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients (by rfl)
        (funext fun k => Frame.PullbackCoherence.sectionRatio_restrict (s i) (s k) h) i _ _)

/-- The absolute section-chart maps agree on each fiber-product overlap of their domains. -/
theorem sectionAbsoluteChart_overlap (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i j : Fin (n + 1)) :
    pullback.fst (Ample.LineBundles.sectionNonvanishing (s i)).ι (Ample.LineBundles.sectionNonvanishing (s j)).ι ≫ sectionAbsoluteChart f s i =
      pullback.snd (Ample.LineBundles.sectionNonvanishing (s i)).ι (Ample.LineBundles.sectionNonvanishing (s j)).ι ≫ sectionAbsoluteChart f s j := by
  let U : X.Opens := Ample.LineBundles.sectionNonvanishing (s i)
  let V : X.Opens := Ample.LineBundles.sectionNonvanishing (s j)
  let W : Scheme.{u} := pullback U.ι V.ι
  let pi : W ⟶ U.toScheme := pullback.fst U.ι V.ι
  let pj : W ⟶ V.toScheme := pullback.snd U.ι V.ι
  let g : W ⟶ X := pi ≫ U.ι
  have hg : g = pj ≫ V.ι := pullback.condition
  have hi : IsIso (Ample.LineBundles.pullbackSection g (s i)) :=
    Frame.PullbackCoherence.pullbackSection_through_nonvanishing_isIso (s i) pi
  have hj' : IsIso (Ample.LineBundles.pullbackSection (pj ≫ V.ι) (s j)) :=
    Frame.PullbackCoherence.pullbackSection_through_nonvanishing_isIso (s j) pj
  have hj : IsIso (Ample.LineBundles.pullbackSection g (s j)) :=
    (congrArg (fun a : W ⟶ X => IsIso (Ample.LineBundles.pullbackSection a (s j))) hg).mpr hj'
  let t (k : Fin (n + 1)) := Ample.LineBundles.pullbackSection g (s k)
  have hi' : IsIso (t i) := hi
  have hj'' : IsIso (t j) := hj
  have hjMap : pj ≫ sectionAbsoluteChart f s j =
      ProjectiveChart.Evaluation.projectiveChartMap (g ≫ f).appTop.hom (fun k => Frame.Coordinates.frameCoordinate (t j) (t k)) j
        (Frame.Coordinates.frameCoordinate_self (t j)) := by
    exact (sectionAbsoluteChart_restrict f s j pj).trans
      (Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients
        (congrArg (fun a : W ⟶ X => (a ≫ f).appTop.hom) hg.symm)
        (funext fun k => Frame.PullbackCoherence.frameCoordinate_pullbackCongr hg.symm (s j) (s k)) j _ _)
  exact (sectionAbsoluteChart_restrict f s i pi).trans
    ((Framed.ProjectiveMaps.projectiveChartMap_frames (g ≫ f).appTop.hom t i j).trans hjMap.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ChartOverlaps
