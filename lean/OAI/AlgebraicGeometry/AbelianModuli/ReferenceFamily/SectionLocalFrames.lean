import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence

/-! # Section Local Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionLocalFrames

noncomputable section

/-! A nonvanishing section supplies an actual local sheaf frame whose
transition is the original regular ratio of sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {M : X.Modules}

def sectionLocalFrame (s : HilbertConstruction.Line.Bundles.structureModule X ⟶ M) : LineFrameAtlas.LocalLineFrame M := by
  have : IsIso (HilbertConstruction.Section.SectionRestriction.restrictSection (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s) :=
    (HilbertConstruction.Local.CoordinateValues.restrictSection_isIso_iff (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s).mpr inferInstance
  exact ⟨HilbertConstruction.Ample.LineBundles.sectionNonvanishing s, (asIso (HilbertConstruction.Section.SectionRestriction.restrictSection (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s)).symm⟩

theorem sectionLocalFrame_one_image (s : HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (W : (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).toScheme.Opens) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnImage M (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (sectionLocalFrame s).frame W
      (s.app ((HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι ''ᵁ W) (1 : Γ(X, _))) = 1 := by
  have : IsIso (HilbertConstruction.Section.SectionRestriction.restrictSection (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s) :=
    (HilbertConstruction.Local.CoordinateValues.restrictSection_isIso_iff (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s).mpr inferInstance
  have h := congrArg (fun a : HilbertConstruction.Line.Bundles.structureModule (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).toScheme ⟶
    HilbertConstruction.Line.Bundles.structureModule (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).toScheme => a.app W (1 : Γ((HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).toScheme, W)))
      (IsIso.hom_inv_id (HilbertConstruction.Section.SectionRestriction.restrictSection (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s))
  change (inv (HilbertConstruction.Section.SectionRestriction.restrictSection (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s)).app W
    ((HilbertConstruction.Section.SectionRestriction.restrictSection (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s).app W (1 : Γ((HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).toScheme, W))) =
      (1 : Γ((HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).toScheme, W)) at h
  exact (congrArg (fun z => (inv (HilbertConstruction.Section.SectionRestriction.restrictSection (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s)).app W z)
    (HilbertConstruction.Section.SectionRestriction.restrictSection_app_one (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι s W)).symm.trans h

theorem transportFrame_section_one (s : HilbertConstruction.Line.Bundles.structureModule X ⟶ M) {U V : X.Opens} (h : U = V)
    (e : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (he : e (s.app U (1 : Γ(X, U))) = 1) :
    DivisorClass.Chern.FramesFrame.Construction.transportFrame M h e (s.app V (1 : Γ(X, V))) = 1 := by
  subst V
  exact he

theorem sectionLocalFrame_one (s : HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (W : X.Opens)
    (hW : W ≤ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    (sectionLocalFrame s).coordinates W hW (s.app W (1 : Γ(X, W))) = 1 :=
  transportFrame_section_one s (DivisorClass.Chern.FramesFrame.Construction.image_preimage_subopen (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) hW)
    (DivisorClass.Chern.FramesFrame.Construction.frameOnImage M (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (sectionLocalFrame s).frame ((HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι ⁻¹ᵁ W))
    (sectionLocalFrame_one_image s ((HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι ⁻¹ᵁ W))

theorem pullbackSection_subopen_isIso (s : HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (W : X.Opens) (hW : W ≤ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) : IsIso (HilbertConstruction.Ample.LineBundles.pullbackSection W.ι s) := by
  have h := HilbertConstruction.Frame.PullbackCoherence.pullbackSection_through_nonvanishing_isIso s (X.homOfLE hW)
  exact (congrArg (fun f => IsIso (HilbertConstruction.Ample.LineBundles.pullbackSection f s)) (Scheme.homOfLE_ι X hW)).mp h

theorem sectionLocalFrame_transition (s t : HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (W : X.Opens)
    (hs : W ≤ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (ht : W ≤ HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) :
    ((sectionLocalFrame s).transition (sectionLocalFrame t) W hs ht : Γ(X, W)) =
      W.topIso.hom ((X.homOfLE hs).appTop (HilbertConstruction.Section.Frames.sectionRatio s t)) := by
  have : IsIso (HilbertConstruction.Ample.LineBundles.pullbackSection W.ι s) := pullbackSection_subopen_isIso s W hs
  let e := (sectionLocalFrame s).coordinates W hs
  let f := (sectionLocalFrame t).coordinates W ht
  have hgen : f.symm 1 = t.app W (1 : Γ(X, W)) := by
    apply f.injective
    exact f.apply_symm_apply 1 |>.trans (sectionLocalFrame_one t W ht).symm
  have hv := congrArg e (HilbertConstruction.CoordinatesOnOpenSubschemes.local_frameCoordinate_value_on_open W s t)
  rw [e.map_smul, sectionLocalFrame_one s W hs, smul_eq_mul, mul_one] at hv
  have hr := (HilbertConstruction.Frame.PullbackCoherence.sectionRatio_restrict s t (X.homOfLE hs)).trans
    (HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackCongr (Scheme.homOfLE_ι X hs) s t)
  change e (f.symm 1) = _
  exact (congrArg e hgen).trans (hv.trans (congrArg (fun z => W.topIso.hom z) hr).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionLocalFrames
