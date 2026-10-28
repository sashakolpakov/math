import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FrameTransport
import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame

/-! # Mixed Frames -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.MixedFrames

noncomputable section

/-!
# ChernClass: compare original frames with frames of the restricted line bundle

The actual section identifications compare the original algebraic atlas
with the restricted sheaf's independently chosen atlas. Their mixed units
satisfy restriction and change-of-frame identities in the actual section rings.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
  (f : Y.carrier ⟶ X.carrier) [IsOpenImmersion f]

local notation "M" => L.restrictToOpen Y f

/-- The original frame, transported to sections of the actual restricted sheaf. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openSectionFrame (i : X.carrier) (W : Y.carrier.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) :
    Γ((M).sheaf, W) ≃ₗ[Γ(Y.carrier, W)] Γ(Y.carrier, W) :=
  FrameTransport.Construction.openImmersionSectionFrame f L.sheaf W (L.sectionFrame i (f ''ᵁ W) hi)

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openSectionFrame_naturality (i : X.carrier) {V W : Y.carrier.Opens}
    (hVW : V ≤ W) (hi : f ''ᵁ W ≤ L.trivializingOpen i) (m : Γ((M).sheaf, W)) :
    L.openSectionFrame f i V ((f.image_mono hVW).trans hi)
        ((M).sheaf.presheaf.map (homOfLE hVW).op m) =
      Y.carrier.presheaf.map (homOfLE hVW).op (L.openSectionFrame f i W hi m) :=
  FrameTransport.Construction.openImmersionSectionFrame_naturality f L.sheaf hVW _ _
    (L.sectionFrame_naturality i (f.image_mono hVW) hi) m

/-- The transported transition is the actual scalar pullback of the original unit. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openSectionFrame_transition (i j : X.carrier) (W : Y.carrier.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : f ''ᵁ W ≤ L.trivializingOpen j) :
    FramesFrame.Construction.frameTransitionUnit (L.openSectionFrame f i W hi) (L.openSectionFrame f j W hj) =
      Units.map (f.appIso W).hom.hom.toMonoidHom
        (L.ambientTransitionOn i j (f ''ᵁ W) hi hj) :=
  FrameTransport.Construction.openImmersionSectionFrame_transition f L.sheaf W _ _

/-- A regular unit comparing an original frame with a native restricted-sheaf frame. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedTransitionOn (i : X.carrier) (j : Y.carrier) (W : Y.carrier.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : W ≤ (M).trivializingOpen j) :
    Γ(Y.carrier, W)ˣ :=
  FramesFrame.Construction.frameTransitionUnit (L.openSectionFrame f i W hi) ((M).sectionFrame j W hj)

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedTransitionOn_restrict (i : X.carrier) (j : Y.carrier)
    {V W : Y.carrier.Opens} (hVW : V ≤ W)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : W ≤ (M).trivializingOpen j) :
    Units.map (Y.carrier.presheaf.map (homOfLE hVW).op).hom.toMonoidHom
      (L.openMixedTransitionOn f i j W hi hj) =
      L.openMixedTransitionOn f i j V ((f.image_mono hVW).trans hi) (hVW.trans hj) :=
  FramesFrame.Construction.frameTransitionUnit_map (Y.carrier.presheaf.map (homOfLE hVW).op).hom
    ((M).sheaf.presheaf.map (homOfLE hVW).op) _ _ _ _
    (L.openSectionFrame_naturality f i hVW hi) ((M).sectionFrame_naturality j hVW hj)

/-- Actual original, restricted, and mixed transitions form a commuting square. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedTransitionOn_square (i j : X.carrier) (k l : Y.carrier)
    (W : Y.carrier.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : f ''ᵁ W ≤ L.trivializingOpen j)
    (hk : W ≤ (M).trivializingOpen k) (hl : W ≤ (M).trivializingOpen l) :
    L.openMixedTransitionOn f i k W hi hk * (M).ambientTransitionOn k l W hk hl =
      Units.map (f.appIso W).hom.hom.toMonoidHom
        (L.ambientTransitionOn i j (f ''ᵁ W) hi hj) *
      L.openMixedTransitionOn f j l W hj hl := by
  rw [← L.openSectionFrame_transition f i j W hi hj]
  exact (FramesFrame.Construction.frameTransitionUnit_cocycle _ _ _).trans (FramesFrame.Construction.frameTransitionUnit_cocycle _ _ _).symm

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.MixedFrames
