import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.OpenCoordinates

/-! # Frame Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameCoordinates

noncomputable section

/-! Pulling back an actual local frame pulls its coordinates back by
the scheme's map on regular sections, on every common subopen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Scheme.Modules

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)

omit f M in
theorem schemeAppLE_congr {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (W : X.Opens)
    (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) : f.appLE U W hf = g.appLE U W hg := by
  subst g
  rfl

theorem pullbackLocalFrame_coordinates (s : LineFrameAtlas.LocalLineFrame M)
    (V : Y.Opens) (hV : V ≤ s.domain) (m : Γ(M, V)) :
    (Local.PullbackFrames.pullbackLocalFrame f M s).coordinates (f ⁻¹ᵁ V) (fun _ hx => hV hx)
      (Global.pullbackSectionMap f M V m) = f.app V (s.coordinates V hV m) := by
  let D := f ⁻¹ᵁ s.domain
  let W := D.ι ⁻¹ᵁ f ⁻¹ᵁ V
  let q := f ∣_ s.domain
  have hW : W ≤ q ⁻¹ᵁ s.domain.ι ⁻¹ᵁ V := (Local.PullbackFrames.localPullback_preimage f s.domain V).symm.le
  have hc := Local.PullbackFrames.localPullbackComparison_sectionsLE f M s.domain V W hW m
  have hg := Global.pullbackGlobalFrame_sectionsLE q s.frame (s.domain.ι ⁻¹ᵁ V) W hW
    (M.presheaf.map (homOfLE (s.domain.ι.image_preimage_le V)).op m)
  have he := (congrArg ((Global.pullbackGlobalFrame q s.frame).hom.app W) hc).trans hg
  have ho := Frame.OpenCoordinates.frameOnOpen_subscheme M s.domain s.frame V hV m
  have he' := he.trans (congrArg (q.appLE (s.domain.ι ⁻¹ᵁ V) W hW) ho)
  have hs : s.domain.ι.app V ≫ q.appLE (s.domain.ι ⁻¹ᵁ V) W hW =
      f.app V ≫ D.ι.app (f ⁻¹ᵁ V) := by
    have hleft := (Scheme.Hom.comp_appLE q s.domain.ι V W hW).symm
    have hq : q ≫ s.domain.ι = D.ι ≫ f := morphismRestrict_ι f s.domain
    exact (hleft.trans (schemeAppLE_congr hq V W hW le_rfl)).trans
      ((Scheme.Hom.comp_appLE D.ι f V W le_rfl).trans
      (congrArg (fun a => f.app V ≫ a) (Scheme.Hom.appLE_eq_app D.ι)))
  apply Frame.OpenCoordinates.openInclusion_app_injective D (f ⁻¹ᵁ V) (fun _ hx => hV hx)
  have ht := Frame.OpenCoordinates.frameOnOpen_subscheme ((pullback f).obj M) D
    (Local.PullbackFrames.pullbackLocalFrame f M s).frame (f ⁻¹ᵁ V) (fun _ hx => hV hx)
    (Global.pullbackSectionMap f M V m)
  exact ht.symm.trans (he'.trans (ConcreteCategory.congr_hom hs (s.coordinates V hV m)))

theorem pullbackLocalFrame_transition (s t : LineFrameAtlas.LocalLineFrame M)
    (V : Y.Opens) (hs : V ≤ s.domain) (ht : V ≤ t.domain) :
    Units.map (f.app V).hom.toMonoidHom (s.transition t V hs ht) =
      (Local.PullbackFrames.pullbackLocalFrame f M s).transition (Local.PullbackFrames.pullbackLocalFrame f M t) (f ⁻¹ᵁ V)
        (fun _ hx => hs hx) (fun _ hx => ht hx) :=
  DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit_map
    (N := Γ((pullback f).obj M, f ⁻¹ᵁ V)) (f.app V).hom
    (Global.pullbackSectionMap f M V) _ _ _ _
    (pullbackLocalFrame_coordinates f M s V hs) (pullbackLocalFrame_coordinates f M t V ht)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.FrameCoordinates
