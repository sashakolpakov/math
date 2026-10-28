import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChainComposition

/-! # Square Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareComposition

noncomputable section

/-! Composition of two actual commuting pullback squares preserves
their native frames, including nonflat scalar and reduction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullbackSquareFrame_horizontal {X Y Z P U V : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (u : P ⟶ X) (a : U ⟶ Y) (b : V ⟶ Z)
    (p : P ⟶ U) (q : U ⟶ V) (h₁ : p ≫ a = u ≫ f) (h₂ : q ≫ b = a ≫ g)
    (h₃ : (p ≫ q) ≫ b = u ≫ (f ≫ g)) (M : Z.Modules)
    (e : (Scheme.Modules.pullback b).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj V) :
    RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f u a p h₁ ((Scheme.Modules.pullback g).obj M)
      (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame g a b q h₂ M e) =
      (Scheme.Modules.pullback u).mapIso ((Scheme.Modules.pullbackComp f g).app M) ≪≫
        RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (f ≫ g) u b (p ≫ q) h₃ M e := by
  have ht : Scheme.Modules.pullbackCongr (congrArg (fun c => c ≫ g) h₁.symm) ≪≫
      Scheme.Modules.pullbackCongr (congrArg (fun c => p ≫ c) h₂.symm) =
        Scheme.Modules.pullbackCongr h₃.symm := by
    exact RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackCongr_trans (congrArg (fun c => c ≫ g) h₁.symm)
      (congrArg (fun c => p ≫ c) h₂.symm)
  have htM := congrArg (fun c => c.app M) ht
  simp only [NatIso.trans_app] at htM
  have hassoc : (Scheme.Modules.pullbackComp u f).app ((Scheme.Modules.pullback g).obj M) ≪≫
      (Scheme.Modules.pullbackComp (u ≫ f) g).app M =
    (Scheme.Modules.pullback u).mapIso ((Scheme.Modules.pullbackComp f g).app M) ≪≫
      (Scheme.Modules.pullbackComp u (f ≫ g)).app M :=
    Iso.ext (RepresentationTheory.Theta.Geometric.Pullback.Associativity.pullbackComp_assoc_app u f g M)
  let C := (Scheme.Modules.pullbackComp (p ≫ a) g).app M
  let D := (Scheme.Modules.pullbackCongr (congrArg (fun c => p ≫ c) h₂.symm)).app M
  have hA := (RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame_assoc p a g
    ((Scheme.Modules.pullbackCongr h₂.symm).app M ≪≫ RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame q b e)).symm
  have hB := congrArg (fun t => C ≪≫ t)
    (RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.factoredPullbackFrame_congr_right p h₂.symm (RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame q b e))
  have hC := congrArg (fun t => C ≪≫ D ≪≫ t) (RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame_comp p q b e)
  have hF := congrArg (fun t => (Scheme.Modules.pullbackComp u f).app ((Scheme.Modules.pullback g).obj M) ≪≫
    (Scheme.Modules.pullbackCongr h₁.symm).app ((Scheme.Modules.pullback g).obj M) ≪≫ t)
      (hA.trans (hB.trans hC))
  exact hF.trans (Frame.ChainComposition.frameChain_composition
    ((Scheme.Modules.pullbackComp u f).app ((Scheme.Modules.pullback g).obj M))
    ((Scheme.Modules.pullbackCongr h₁.symm).app ((Scheme.Modules.pullback g).obj M)) C D
    (RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame (p ≫ q) b e) ((Scheme.Modules.pullbackComp (u ≫ f) g).app M)
    ((Scheme.Modules.pullbackCongr (congrArg (fun c => c ≫ g) h₁.symm)).app M)
    ((Scheme.Modules.pullback u).mapIso ((Scheme.Modules.pullbackComp f g).app M))
    ((Scheme.Modules.pullbackComp u (f ≫ g)).app M) ((Scheme.Modules.pullbackCongr h₃.symm).app M)
    (RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackComp_congr_left h₁.symm g M) hassoc htM)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareComposition
