import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameApps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence

/-! # Frame Coordinate Pullback -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction

noncomputable section

/-! Frame coordinates under arbitrary scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem frameCoordinate_pullback_any {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (s t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso s] :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f t) =
      f.appTop (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate s t) := by
  have he : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f t) =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫
        (Scheme.Modules.pullback f).map (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t) ≫
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
    apply (cancel_mono (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)).mp
    rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd_frame]
    simp only [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd, Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) he).trans
    (AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd s t))

def sectionAppCoordinate {X : Scheme.{u}} {M : X.Modules}
    (s t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U : X.Opens} (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) : Γ(X, U) :=
  (SectionFrameApps.Construction.sectionAppLinearEquiv s hU).symm (t.app U (1 : Γ(X, U)))

theorem sectionAppCoordinate_smul {X : Scheme.{u}} {M : X.Modules}
    (s t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U : X.Opens} (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (r : Γ(X, U)) :
    (SectionFrameApps.Construction.sectionAppLinearEquiv s hU).symm (t.app U r) = r * sectionAppCoordinate s t hU := by
  have ht : t.app U r = r • t.app U (1 : Γ(X, U)) := by
    have he := t.app_smul r (1 : Γ(X, U))
    change t.app U (show Γ(X, U) from r * 1) = r • t.app U (1 : Γ(X, U)) at he
    exact (congrArg (fun z : Γ(X, U) => t.app U z) (mul_one r)).symm.trans he
  rw [ht, map_smul]
  rfl

theorem sectionAppCoordinate_restrict {X : Scheme.{u}} {M : X.Modules}
    (s t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U V : X.Opens} (h : V ≤ U)
    (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    X.presheaf.map (homOfLE h).op (sectionAppCoordinate s t hU) =
      sectionAppCoordinate s t (h.trans hU) := by
  have ht : M.presheaf.map (homOfLE h).op (t.app U (1 : Γ(X, U))) =
      t.app V (1 : Γ(X, V)) := by
    have hn := PresheafOfModules.naturality_apply t.val (homOfLE h).op (1 : Γ(X, U))
    exact hn.symm.trans (congrArg (fun r : Γ(X, V) => t.app V r)
      ((X.presheaf.map (homOfLE h).op).hom.map_one))
  exact (SectionFrameApps.Construction.sectionAppLinearEquiv_symm_restrict s h hU (t.app U (1 : Γ(X, U)))).trans
    (congrArg (SectionFrameApps.Construction.sectionAppLinearEquiv s (h.trans hU)).symm ht)

theorem sectionAppCoordinate_eq_frameCoordinate {X : Scheme.{u}} {M : X.Modules}
    (s t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U : X.Opens} (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    letI := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hU s
    sectionAppCoordinate s t hU = U.topIso.hom
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι t)) := by
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hU s
  let c := U.topIso.hom (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι t))
  apply (SectionFrameApps.Construction.sectionAppLinearEquiv s hU).injective
  have he : s.app U c = c • s.app U (1 : Γ(X, U)) := by
    have hh := s.app_smul c (1 : Γ(X, U))
    change s.app U (show Γ(X, U) from c * 1) = c • s.app U (1 : Γ(X, U)) at hh
    exact (congrArg (fun r : Γ(X, U) => s.app U r) (mul_one c)).symm.trans hh
  exact ((SectionFrameApps.Construction.sectionAppLinearEquiv s hU).apply_symm_apply (t.app U (1 : Γ(X, U)))).trans
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes.local_frameCoordinate_value_on_open U s t).trans he.symm)

theorem sectionRatio_pullback_any {X Y : Scheme.{u}} {M : Y.Modules}
    (s t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) (h : X ⟶ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).toScheme) :
    h.appTop (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio s t) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (h ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι) s)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (h ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι) t) :=
  (congrArg h.appTop (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.sectionRatio_eq_frameCoordinate s t)).trans
    ((frameCoordinate_pullback_any h (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι t)).symm.trans
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackComp (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι h s t).symm)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction
