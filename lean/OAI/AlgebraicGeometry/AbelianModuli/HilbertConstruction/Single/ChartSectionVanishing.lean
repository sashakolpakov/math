import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSectionZero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullback

/-! # Chart Section Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ChartSectionVanishing

noncomputable section

/-! When a scheme map lands in a single frame chart, its pulled-back
section vanishes exactly when the global pulled-back chart coefficient
vanishes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}}

theorem openSectionPullback_eq_zero_iff_of_top (f : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (r : Γ(Y, U)) :
    Open.SectionPullback.openSectionPullback f U ⊤ h r = 0 ↔ f.app U r = 0 := by
  have : IsIso (homOfLE h) := by
    have he : homOfLE h = eqToHom (top_unique h).symm := Subsingleton.elim _ _
    rw [he]
    infer_instance
  have hinj := (ConcreteCategory.bijective_of_isIso (X.presheaf.map (homOfLE h).op)).injective
  constructor
  · intro hr
    apply hinj
    change X.presheaf.map (homOfLE h).op (f.app U r) = 0 at hr
    exact hr.trans (map_zero _).symm
  · intro hr
    change X.presheaf.map (homOfLE h).op (f.app U r) = 0
    rw [hr, map_zero]

theorem openFrame_pullbackSection_eq_zero_iff_single_chart
    {ι : Type u} {U : ι → Y.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U) (f : X ⟶ Y)
    (hU : ∀ y : Y, ∃ i, y ∈ U i)
    (s : Line.Bundles.structureModule Y ⟶ OpenFrame.ModuleSheaf.openFrameModuleSheaf D) (i : ι) (hi : ⊤ ≤ f ⁻¹ᵁ U i) :
    Ample.LineBundles.pullbackSection f s = 0 ↔ Open.SectionPullback.openSectionPullback f (U i) ⊤ hi
      (OpenFrame.CoefficientSections.openFrameGlobalTupleMap D (Global.Sections.moduleSectionHomEquiv (OpenFrame.ModuleSheaf.openFrameModuleSheaf D) s) i) = 0 := by
  rw [openSectionPullback_eq_zero_iff_of_top]
  constructor
  · intro hs
    exact (OpenFrame.PullbackSectionZero.openFrame_pullbackSection_eq_zero_iff D f hU s).mp hs i
  · intro hs
    let c := OpenFrame.PullbackSheafMap.openFramePullbackComparison D f
    have : IsIso c := (OpenFrame.PullbackIsomorphism.openFramePullbackIso D f hU).isIso_hom
    apply (cancel_mono c).mp
    rw [zero_comp]
    apply Section.EqualityAndPullbackValues.moduleSection_eq_of_cover (OpenFrame.ModuleSheaf.openFrameModuleSheaf (D.pullback f))
      (fun _ : Unit => f ⁻¹ᵁ U i) (fun x => ⟨(), hi (show x ∈ (⊤ : X.Opens) from trivial)⟩)
    intro _
    change c.app (f ⁻¹ᵁ U i) ((Ample.LineBundles.pullbackSection f s).app (f ⁻¹ᵁ U i)
      (1 : Γ(X, f ⁻¹ᵁ U i))) = 0
    rw [show c = OpenFrame.PullbackSheafMap.openFramePullbackComparison D f from rfl,
      OpenFrame.PullbackSectionZero.openFramePullbackSection_app_of_tuple, hs]
    exact (OpenFrame.LocalFreeness.openFrameLocalEquiv (D.pullback f) (f ⁻¹ᵁ U i) i le_rfl).map_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ChartSectionVanishing
