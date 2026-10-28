import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback

/-! # Section Coordinate Pullback -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionCoordinatePullback

noncomputable section

/-! Local frame coordinates of actual sections commute with the scheme's native map on open sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction

theorem sectionAppCoordinate_pullbackLE {X Y : Scheme.{0}} (f : X ⟶ Y) {M : Y.Modules}
    (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) (U : Y.Opens) (V : X.Opens)
    (hUV : V ≤ f ⁻¹ᵁ U) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)
    (hV : V ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) :
    ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f t) hV =
      f.appLE U V hUV (ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate s t hU) := by
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hU s
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) := AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hV _
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (V.ι ≫ f) s) :=
    (AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff f V.ι s).mp inferInstance
  let q := f.resLE U V hUV
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s)) := inferInstance
  have : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (q ≫ U.ι) s) :=
    (AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff U.ι q s).mp inferInstance
  have hr : AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s))
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f t)) =
      q.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι t)) :=
    (AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackComp f V.ι s t).symm.trans
      ((AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackCongr (f.resLE_comp_ι hUV).symm s t).trans
        ((AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackComp U.ι q s t).trans
          (ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.frameCoordinate_pullback_any q (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι t))))
  rw [ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate_eq_frameCoordinate _ _ hV,
    ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate_eq_frameCoordinate _ _ hU, hr]
  change V.topIso.hom ((f.resLE U V hUV).app ⊤ _) = _
  rw [Scheme.Hom.resLE_app_top]
  simp only [ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom V.topIso.inv_hom_id _

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionCoordinatePullback
