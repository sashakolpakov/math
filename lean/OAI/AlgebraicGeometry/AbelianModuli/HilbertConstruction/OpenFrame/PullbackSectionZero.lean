import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionCoordinateValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EqualityAndPullbackValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames

/-! # Pullback Section Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSectionZero

noncomputable section

/-! Actual pullback of a section of a framed line bundle is zero
exactly when all of its pulled-back regular chart coefficients are
zero. This uses sheaf values, including nilpotent coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens}
variable (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)

theorem openFramePullbackSection_app_of_tuple
    (s : Line.Bundles.structureModule Y ⟶ ModuleSheaf.openFrameModuleSheaf D) (i : ι) :
    (PullbackSheafMap.openFramePullbackComparison D f).app (f ⁻¹ᵁ U i)
      ((Ample.LineBundles.pullbackSection f s).app (f ⁻¹ᵁ U i) (1 : Γ(X, f ⁻¹ᵁ U i))) =
        SectionGenerators.openFrameGenerator (D.pullback f) (f ⁻¹ᵁ U i) i le_rfl
          (f.app (U i) (CoefficientSections.openFrameGlobalTupleMap D
            (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) i)) := by
  rw [Section.EqualityAndPullbackValues.pullbackSection_value_on_preimage]
  have h := congrArg (fun a : ModuleSheaf.openFrameModuleSheaf D ⟶
      (Scheme.Modules.pushforward f).obj (ModuleSheaf.openFrameModuleSheaf (D.pullback f)) =>
      a.app (U i) (s.app (U i) (1 : Γ(Y, U i)))) (PullbackIsomorphism.openFramePullbackComparison_unit D f)
  change (PullbackSheafMap.openFramePullbackComparison D f).app (f ⁻¹ᵁ U i)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ModuleSheaf.openFrameModuleSheaf D)).app
      (U i) (s.app (U i) (1 : Γ(Y, U i)))) =
        (PullbackSheafMap.openFramePullbackAdjoint D f).app (U i) (s.app (U i) (1 : Γ(Y, U i))) at h
  rw [h, SectionCoordinateValues.openFrameSection_app_of_tuple]
  exact PullbackGenerators.openFrameSectionPullback_generator D f (U i) i le_rfl _

theorem openFrame_pullbackSection_eq_zero_iff
    (hU : ∀ y : Y, ∃ i, y ∈ U i)
    (s : Line.Bundles.structureModule Y ⟶ ModuleSheaf.openFrameModuleSheaf D) :
    Ample.LineBundles.pullbackSection f s = 0 ↔ ∀ i, f.app (U i)
      (CoefficientSections.openFrameGlobalTupleMap D (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) i) = 0 := by
  constructor
  · intro hs i
    apply LocalFreeness.openFrameGenerator_injective (D.pullback f) (f ⁻¹ᵁ U i) i le_rfl
    have h := openFramePullbackSection_app_of_tuple D f s i
    rw [hs] at h
    have hz : (0 : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (ModuleSheaf.openFrameModuleSheaf D)).app
        (f ⁻¹ᵁ U i) (1 : Γ(X, f ⁻¹ᵁ U i)) = 0 := rfl
    rw [hz, map_zero] at h
    exact h.symm.trans (LocalFreeness.openFrameLocalEquiv (D.pullback f) (f ⁻¹ᵁ U i) i le_rfl).map_zero.symm
  · intro hs
    let c := PullbackSheafMap.openFramePullbackComparison D f
    have : IsIso c := (PullbackIsomorphism.openFramePullbackIso D f hU).isIso_hom
    apply (cancel_mono c).mp
    rw [zero_comp]
    apply Section.EqualityAndPullbackValues.moduleSection_eq_of_cover (ModuleSheaf.openFrameModuleSheaf (D.pullback f)) (fun i => f ⁻¹ᵁ U i)
      (PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover f hU)
    intro i
    change c.app (f ⁻¹ᵁ U i) ((Ample.LineBundles.pullbackSection f s).app (f ⁻¹ᵁ U i)
      (1 : Γ(X, f ⁻¹ᵁ U i))) = 0
    rw [show c = PullbackSheafMap.openFramePullbackComparison D f from rfl,
      openFramePullbackSection_app_of_tuple, hs i]
    exact (LocalFreeness.openFrameLocalEquiv (D.pullback f) (f ⁻¹ᵁ U i) i le_rfl).map_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSectionZero
