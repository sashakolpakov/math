import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Square Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareCongruence

noncomputable section

/-! Equality of the actual base maps transports a native square
frame through the original pullback comparison isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullbackSquareFrame_congr {X Y U P : Scheme.{0}}
    {f f' : X ⟶ Y} (hf : f = f') (u : P ⟶ X) (a : U ⟶ Y)
    {p p' : P ⟶ U} (hp : p = p') (h : p ≫ a = u ≫ f) (h' : p' ≫ a = u ≫ f')
    (M : Y.Modules) (e : (Scheme.Modules.pullback a).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U) :
    RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f u a p h M e =
      (Scheme.Modules.pullback u).mapIso ((Scheme.Modules.pullbackCongr hf).app M) ≪≫
        RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f' u a p' h' M e := by
  subst f'
  subst p'
  simp only [RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackCongr_refl_app, Functor.mapIso_refl, Iso.refl_trans]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareCongruence
