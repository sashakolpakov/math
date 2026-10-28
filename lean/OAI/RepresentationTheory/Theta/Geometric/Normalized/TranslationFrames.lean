import OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoPullback
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Translation Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.TranslationFrames

noncomputable section

/-! A normalized translation comparison preserves the induced frame
on every test point of the normalization axis. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem factoredPullbackFrame_mapIso {X Y T : Scheme.{u}} (v : T ⟶ Y) (i : Y ⟶ X)
    {M N : X.Modules} (φ : M ≅ N)
    (e : (Scheme.Modules.pullback i).obj N ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    (Scheme.Modules.pullback (v ≫ i)).mapIso φ ≪≫ FactoredPullbackFrames.factoredPullbackFrame v i e =
      FactoredPullbackFrames.factoredPullbackFrame v i ((Scheme.Modules.pullback i).mapIso φ ≪≫ e) := by
  apply Iso.ext
  simp only [FactoredPullbackFrames.factoredPullbackFrame, Pullback.FrameComposition.pullbackGlobalFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  erw [(Scheme.Modules.pullbackComp v i).inv.naturality_assoc φ.hom]
  rfl

theorem normalizedTranslation_fiber_frame {X Y T : Scheme.{u}} (M : X.Modules)
    (t : X ⟶ X) (i : Y ⟶ X) (a : Y ⟶ Y) (hi : a ≫ i = i ≫ t)
    (e : (Scheme.Modules.pullback i).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
    (θ : (Scheme.Modules.pullback t).obj M ≅ M)
    (hθ : (Scheme.Modules.pullback i).mapIso θ ≪≫ e = Pullback.SquareFrames.pullbackSquareFrame t i i a hi M e)
    (v : T ⟶ Y) (hv : (v ≫ a) ≫ i = (v ≫ i) ≫ t) :
    LocallyTranslatedLineIso.translatedMapLineIso M t θ (v ≫ i) ((v ≫ a) ≫ i) hv ≪≫ FactoredPullbackFrames.factoredPullbackFrame v i e =
      FactoredPullbackFrames.factoredPullbackFrame (v ≫ a) i e := by
  have H := congrArg (FactoredPullbackFrames.factoredPullbackFrame v i) hθ
  rw [← factoredPullbackFrame_mapIso] at H
  unfold Pullback.SquareFrames.pullbackSquareFrame at H
  rw [← FactoredPullbackFrames.factoredPullbackFrame_assoc v i t] at H
  rw [Pullback.FrameEqualities.factoredPullbackFrame_congr_right v hi.symm, FactoredPullbackFrames.factoredPullbackFrame_comp] at H
  unfold LocallyTranslatedLineIso.translatedMapLineIso
  simp only [Iso.trans_assoc]
  rw [H]
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  have hc : (Scheme.Modules.pullbackCongr hv).app M ≪≫
      (Scheme.Modules.pullbackCongr (congrArg (fun f => v ≫ f) hi.symm)).app M = Iso.refl _ := by
    rw [← NatIso.trans_app, Pullback.FrameEqualities.pullbackCongr_trans]
    exact Pullback.FrameEqualities.pullbackCongr_refl_app _ M
  rw [hc, Iso.refl_trans]

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.TranslationFrames
