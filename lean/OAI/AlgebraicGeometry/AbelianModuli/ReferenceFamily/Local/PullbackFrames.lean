import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.Global
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

/-! # Pullback Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames

noncomputable section

/-! Local frames of an actual module sheaf pull back to frames on the
preimages of their domains, through the canonical sheaf pullback maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Scheme.Modules

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)

def localPullbackComparison :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      (pullback (f ∣_ U)).obj (M.restrict U.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((pullback f).obj M) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    (pullbackComp (f ∣_ U) U.ι).symm.app M ≪≫
    (pullback (f ∣_ U)).mapIso ((restrictFunctorIsoPullback U.ι).symm.app M)

def pullbackLocalFrame (s : LineFrameAtlas.LocalLineFrame M) : LineFrameAtlas.LocalLineFrame ((pullback f).obj M) where
  domain := f ⁻¹ᵁ s.domain
  frame := localPullbackComparison f M s.domain ≪≫ Pullback.Global.pullbackGlobalFrame (f ∣_ s.domain) s.frame

theorem localPullback_preimage (V : Y.Opens) :
    (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V = (f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ V :=
  congrArg (fun a : (f ⁻¹ᵁ U).toScheme ⟶ Y => a ⁻¹ᵁ V) (morphismRestrict_ι f U)

theorem localPullbackComparison_sectionsLE (V : Y.Opens) (W : (f ⁻¹ᵁ U).toScheme.Opens)
    (h : W ≤ (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ V) (m : Γ(M, V)) :
    (localPullbackComparison f M U).hom.app W
      (Pullback.Global.pullbackSectionMapLE f M V
        ((f ⁻¹ᵁ U).ι ''ᵁ W)
        (by rintro _ ⟨x, hx, rfl⟩; exact (localPullback_preimage f U V).le (h hx)) m) =
    Pullback.Global.pullbackSectionMapLE (f ∣_ U) (M.restrict U.ι) (U.ι ⁻¹ᵁ V) W h
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op m) := by
  have hW : W ≤ (f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ V := h.trans (localPullback_preimage f U V).le
  have h₁ := Pullback.Global.restrictionPullback_hom_sectionLE (f ⁻¹ᵁ U).ι ((pullback f).obj M)
    (f ⁻¹ᵁ V) W hW (Pullback.Global.pullbackSectionMap f M V m)
  change ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).hom.app ((pullback f).obj M)).app W
    (Pullback.Global.pullbackSectionMapLE f M V ((f ⁻¹ᵁ U).ι ''ᵁ W) _ m) = _ at h₁
  change ((pullback (f ∣_ U)).map ((restrictFunctorIsoPullback U.ι).inv.app M)).app W
    (((pullbackComp (f ∣_ U) U.ι).inv.app M).app W
      (((pullbackCongr (morphismRestrict_ι f U).symm).hom.app M).app W
        (((pullbackComp (f ⁻¹ᵁ U).ι f).hom.app M).app W
          (((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).hom.app ((pullback f).obj M)).app W _)))) = _
  rw [h₁]
  have h₂ := Pullback.Global.pullbackComp_hom_sectionLE (f ⁻¹ᵁ U).ι f M V W hW m
  rw [h₂]
  have h₃ := Pullback.Global.pullbackCongr_hom_sectionLE (morphismRestrict_ι f U).symm M V W hW h m
  rw [h₃]
  have h₄ := Pullback.Global.pullbackComp_inv_sectionLE (f ∣_ U) U.ι M V W h m
  rw [h₄]
  have h₅ := Pullback.Global.pullbackSectionMapLE_morphism (f ∣_ U)
    ((restrictFunctorIsoPullback U.ι).inv.app M) (U.ι ⁻¹ᵁ V) W h
    (Pullback.Global.pullbackSectionMap U.ι M V m)
  rw [h₅, Pullback.Global.restrictionPullback_inv_section]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.PullbackFrames
