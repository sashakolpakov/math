import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Square Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareComposition

noncomputable section

/-! Vertical composition of the native normalized pullback squares. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackSquareFrame_comp {X Y Z U V W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : U ⟶ X) (j : V ⟶ Y) (k : W ⟶ Z)
    (a : U ⟶ V) (b : V ⟶ W) (h₁ : a ≫ j = i ≫ f) (h₂ : b ≫ k = j ≫ g)
    (h₃ : (a ≫ b) ≫ k = i ≫ (f ≫ g)) (M : Z.Modules)
    (e : (Scheme.Modules.pullback k).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj W) :
    SquareFrames.pullbackSquareFrame f i j a h₁ ((Scheme.Modules.pullback g).obj M)
        (SquareFrames.pullbackSquareFrame g j k b h₂ M e) =
      (Scheme.Modules.pullback i).mapIso ((Scheme.Modules.pullbackComp f g).app M) ≪≫
        SquareFrames.pullbackSquareFrame (f ≫ g) i k (a ≫ b) h₃ M e := by
  have hc :
      Scheme.Modules.pullbackCongr (congrArg (fun c => c ≫ g) h₁.symm) ≪≫
        Scheme.Modules.pullbackCongr (congrArg (fun c => a ≫ c) h₂.symm) =
      Scheme.Modules.pullbackCongr h₃.symm := by
    simp only [FrameEqualities.pullbackCongr_trans]
  have hcM := congrArg (fun c => c.app M) hc
  simp only [NatIso.trans_app] at hcM
  unfold SquareFrames.pullbackSquareFrame
  rw [← FactoredPullbackFrames.factoredPullbackFrame_assoc a j g]
  rw [FrameEqualities.factoredPullbackFrame_congr_right a h₂.symm, FactoredPullbackFrames.factoredPullbackFrame_comp]
  rw [← Iso.trans_assoc ((Scheme.Modules.pullbackCongr h₁.symm).app
    ((Scheme.Modules.pullback g).obj M)) ((Scheme.Modules.pullbackComp (a ≫ j) g).app M)]
  rw [FrameEqualities.pullbackComp_congr_left h₁.symm g M]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc ((Scheme.Modules.pullbackCongr
      (congrArg (fun c => c ≫ g) h₁.symm)).app M), hcM]
  have hassoc :
      (Scheme.Modules.pullbackComp i f).app ((Scheme.Modules.pullback g).obj M) ≪≫
        (Scheme.Modules.pullbackComp (i ≫ f) g).app M =
      (Scheme.Modules.pullback i).mapIso ((Scheme.Modules.pullbackComp f g).app M) ≪≫
        (Scheme.Modules.pullbackComp i (f ≫ g)).app M :=
    Iso.ext (Associativity.pullbackComp_assoc_app i f g M)
  simpa only [Iso.trans_assoc] using congrArg
    (fun d => d ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app M ≪≫
      FactoredPullbackFrames.factoredPullbackFrame (a ≫ b) k e) hassoc

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareComposition
