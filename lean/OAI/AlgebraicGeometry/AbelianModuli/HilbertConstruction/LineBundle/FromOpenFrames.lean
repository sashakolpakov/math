import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections

/-! # From Open Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames

noncomputable section

/-! An actual regular-function cocycle on an open cover constructs a line bundle, with its local trivializations proved from the explicit frame section maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U)

theorem openFrameLocalSection_app_bijective (k : ι) (W : (U k).toScheme.Opens) :
    Function.Bijective ((OpenFrame.LocalSections.openFrameLocalSection D k).app W) := by
  let g := OpenFrame.SectionGenerators.openFrameGenerator D ((U k).ι ''ᵁ W) k (OpenFrame.LocalSections.openInclusionImage_le (U k) W)
  have hg : Function.Bijective g :=
    ⟨OpenFrame.LocalFreeness.openFrameGenerator_injective D _ _ _, OpenFrame.LocalFreeness.openFrameGenerator_surjective D _ _ _⟩
  have he : (fun r : Γ((U k).toScheme, W) => (OpenFrame.LocalSections.openFrameLocalSection D k).app W r) =
      fun r : Γ((U k).toScheme, W) => g (((U k).ι.appIso W).inv r) :=
    funext (OpenFrame.LocalSections.openFrameLocalSection_app D k W)
  change Function.Bijective (fun r : Γ((U k).toScheme, W) => (OpenFrame.LocalSections.openFrameLocalSection D k).app W r)
  exact (congrArg Function.Bijective he).mpr
    (hg.comp (ConcreteCategory.bijective_of_isIso ((U k).ι.appIso W).inv))

instance openFrameLocalSection_isIso (k : ι) : IsIso (OpenFrame.LocalSections.openFrameLocalSection D k) := by
  have (W : ((U k).toScheme.Opens)ᵒᵖ) : IsIso ((OpenFrame.LocalSections.openFrameLocalSection D k).mapPresheaf.app W) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (openFrameLocalSection_app_bijective D k W.unop)
  have : IsIso (OpenFrame.LocalSections.openFrameLocalSection D k).mapPresheaf := NatIso.isIso_of_isIso_app _
  have : IsIso ((Scheme.Modules.toPresheaf (U k).toScheme).map (OpenFrame.LocalSections.openFrameLocalSection D k)) := this
  exact isIso_of_reflects_iso (OpenFrame.LocalSections.openFrameLocalSection D k) (Scheme.Modules.toPresheaf (U k).toScheme)

def lineBundleFromOpenFrames (hU : ∀ x : X, ∃ i, x ∈ U i) : Line.Bundles.LineBundle X where
  sheaf := OpenFrame.ModuleSheaf.openFrameModuleSheaf D
  locallyTrivial x := by
    obtain ⟨i, hi⟩ := hU x
    exact ⟨U i, hi, ⟨(Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app (OpenFrame.ModuleSheaf.openFrameModuleSheaf D) ≪≫
      (asIso (OpenFrame.LocalSections.openFrameLocalSection D i)).symm⟩⟩

def lineBundleFromOpenFrames_chartIso (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    ((lineBundleFromOpenFrames D hU).pullback (U i).ι).sheaf ≅ Line.Bundles.structureModule (U i).toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app (OpenFrame.ModuleSheaf.openFrameModuleSheaf D) ≪≫
    (asIso (OpenFrame.LocalSections.openFrameLocalSection D i)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames
