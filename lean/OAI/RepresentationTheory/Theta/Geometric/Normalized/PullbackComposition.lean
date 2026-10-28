import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareComposition
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareNaturality

/-! # Pullback Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.PullbackComposition

noncomputable section

/-! Composing normalized isomorphisms preserves their native square
normalization, including all pullback comparison maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def composePullbackIso {X : Scheme.{u}} (f g : X ⟶ X) {M : X.Modules}
    (ef : (Scheme.Modules.pullback f).obj M ≅ M)
    (eg : (Scheme.Modules.pullback g).obj M ≅ M) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ M :=
  ((Scheme.Modules.pullbackComp f g).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso eg ≪≫ ef

theorem pullbackSquareFrame_congr {X Y : Scheme.{u}} {f f' : X ⟶ X} (hf : f = f')
    (i : Y ⟶ X) {a a' : Y ⟶ Y} (ha : a = a')
    (h : a ≫ i = i ≫ f) (h' : a' ≫ i = i ≫ f') (M : X.Modules)
    (e : (Scheme.Modules.pullback i).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    Pullback.SquareFrames.pullbackSquareFrame f i i a h M e =
      (Scheme.Modules.pullback i).mapIso ((Scheme.Modules.pullbackCongr hf).app M) ≪≫
        Pullback.SquareFrames.pullbackSquareFrame f' i i a' h' M e := by
  cases hf
  cases ha
  simp only [Pullback.FrameEqualities.pullbackCongr_refl_app, Functor.mapIso_refl, Iso.refl_trans]

theorem composePullbackIso_normalized {X Y : Scheme.{u}} (f g : X ⟶ X)
    (i : Y ⟶ X) (a b : Y ⟶ Y)
    (h₁ : a ≫ i = i ≫ f) (h₂ : b ≫ i = i ≫ g)
    (h₃ : (a ≫ b) ≫ i = i ≫ (f ≫ g)) (M : X.Modules)
    (e : (Scheme.Modules.pullback i).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
    (ef : (Scheme.Modules.pullback f).obj M ≅ M)
    (eg : (Scheme.Modules.pullback g).obj M ≅ M)
    (hf : (Scheme.Modules.pullback i).mapIso ef ≪≫ e = Pullback.SquareFrames.pullbackSquareFrame f i i a h₁ M e)
    (hg : (Scheme.Modules.pullback i).mapIso eg ≪≫ e = Pullback.SquareFrames.pullbackSquareFrame g i i b h₂ M e) :
    (Scheme.Modules.pullback i).mapIso (composePullbackIso f g ef eg) ≪≫ e =
      Pullback.SquareFrames.pullbackSquareFrame (f ≫ g) i i (a ≫ b) h₃ M e := by
  have hn := Pullback.SquareNaturality.pullbackSquareFrame_naturality f i i a h₁ eg e
  rw [hg, Pullback.SquareComposition.pullbackSquareFrame_comp f g i i i a b h₁ h₂ h₃ M e] at hn
  unfold composePullbackIso
  simp only [Functor.mapIso_trans, Iso.trans_assoc]
  rw [hf, hn]
  simp only [← Iso.trans_assoc, ← Functor.mapIso_trans, Iso.symm_self_id,
    Functor.mapIso_refl, Iso.refl_trans]

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.PullbackComposition
