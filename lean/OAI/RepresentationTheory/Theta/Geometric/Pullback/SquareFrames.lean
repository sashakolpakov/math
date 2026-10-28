import OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities

/-! # Square Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

noncomputable section

/-! Pullback frames on commuting squares, proved before specializing the
schemes to nested opens. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def pullbackSquareFrame {X Y U P : Scheme.{u}} (f : X ⟶ Y) (u : P ⟶ X)
    (a : U ⟶ Y) (p : P ⟶ U) (h : p ≫ a = u ≫ f) (M : Y.Modules)
    (e : (Scheme.Modules.pullback a).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U) :
    (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback f).obj M) ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj P :=
  (Scheme.Modules.pullbackComp u f).app M ≪≫ (Scheme.Modules.pullbackCongr h.symm).app M ≪≫
    FactoredPullbackFrames.factoredPullbackFrame p a e

theorem pullbackSquareFrame_nested {X Y U V P Q : Scheme.{u}}
    (f : X ⟶ Y) (u : P ⟶ X) (v : Q ⟶ X) (a : U ⟶ Y) (b : V ⟶ Y)
    (j : Q ⟶ P) (k : V ⟶ U) (p : P ⟶ U) (q : Q ⟶ V)
    (hX : j ≫ u = v) (hY : k ≫ a = b) (hP : p ≫ a = u ≫ f) (hQ : q ≫ b = v ≫ f)
    (hjk : q ≫ k = j ≫ p) (M : Y.Modules)
    (e : (Scheme.Modules.pullback a).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U) :
    (Scheme.Modules.pullbackCongr hX.symm).app ((Scheme.Modules.pullback f).obj M) ≪≫
      FactoredPullbackFrames.factoredPullbackFrame j u (pullbackSquareFrame f u a p hP M e) =
    pullbackSquareFrame f v b q hQ M
      ((Scheme.Modules.pullbackCongr hY.symm).app M ≪≫ FactoredPullbackFrames.factoredPullbackFrame k a e) := by
  have ht :
      Scheme.Modules.pullbackCongr (congrArg (fun c => c ≫ f) hX.symm) ≪≫
        Scheme.Modules.pullbackCongr (congrArg (fun c => j ≫ c) hP.symm) ≪≫
        Scheme.Modules.pullbackCongr (congrArg (fun c => c ≫ a) hjk.symm) =
      Scheme.Modules.pullbackCongr hQ.symm ≪≫
        Scheme.Modules.pullbackCongr (congrArg (fun c => q ≫ c) hY.symm) := by
    simp only [FrameEqualities.pullbackCongr_trans]
  have htM := congrArg (fun c => c.app M) ht
  simp only [NatIso.trans_app] at htM
  unfold pullbackSquareFrame
  rw [← FactoredPullbackFrames.factoredPullbackFrame_assoc j u f]
  rw [FrameEqualities.factoredPullbackFrame_congr_right j hP.symm, FactoredPullbackFrames.factoredPullbackFrame_comp]
  rw [FrameEqualities.factoredPullbackFrame_congr_right q hY.symm, FactoredPullbackFrames.factoredPullbackFrame_comp]
  rw [FrameEqualities.factoredPullbackFrame_congr_left hjk.symm a]
  simp only [← Iso.trans_assoc]
  rw [FrameEqualities.pullbackComp_congr_left hX.symm f M]
  have hh := congrArg (fun c => (Scheme.Modules.pullbackComp v f).app M ≪≫ c ≪≫
    FactoredPullbackFrames.factoredPullbackFrame (q ≫ k) a e) htM
  simpa only [Iso.trans_assoc] using hh

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames
