import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Square Pullback Global Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquarePullbackGlobalFrames

noncomputable section

/-! Pulling a global frame through an actual commuting square agrees
with the original iterated global pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullbackGlobalFrame_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (e : M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    (Scheme.Modules.pullbackCongr h).app M ≪≫ RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame g e =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e := by
  cases h
  rfl

theorem pullbackGlobalFrame_precomp {X Y : Scheme.{0}} (f : X ⟶ Y) {M N : Y.Modules}
    (q : M ≅ N) (e : N ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f (q ≪≫ e) =
      (Scheme.Modules.pullback f).mapIso q ≪≫ RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e := by
  simp only [RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame, Functor.mapIso_trans, Iso.trans_assoc]

theorem squarePullbackGlobalFrame {X Y U V : Scheme.{0}}
    (f : X ⟶ Y) (i : V ⟶ X) (j : U ⟶ Y) (p : V ⟶ U) (h : p ≫ j = i ≫ f)
    (M : Y.Modules) (e : M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f i j p h M (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame j e) =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame i (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e) := by
  unfold RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame
  rw [← RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame_comp p j e]
  simp only [Iso.symm_self_id_assoc]
  rw [pullbackGlobalFrame_congr, RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquarePullbackGlobalFrames
