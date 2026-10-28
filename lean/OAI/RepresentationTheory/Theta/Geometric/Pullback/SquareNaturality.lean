import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Square Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareNaturality

noncomputable section

/-! Native square frames respect isomorphisms of the original module. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackSquareFrame_naturality {X Y U P : Scheme.{u}} (f : X ⟶ Y) (i : P ⟶ X)
    (j : U ⟶ Y) (a : P ⟶ U) (h : a ≫ j = i ≫ f) {M N : Y.Modules} (φ : M ≅ N)
    (e : (Scheme.Modules.pullback j).obj N ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U) :
    (Scheme.Modules.pullback i).mapIso ((Scheme.Modules.pullback f).mapIso φ) ≪≫
      SquareFrames.pullbackSquareFrame f i j a h N e =
    SquareFrames.pullbackSquareFrame f i j a h M ((Scheme.Modules.pullback j).mapIso φ ≪≫ e) := by
  apply Iso.ext
  simp only [SquareFrames.pullbackSquareFrame, FactoredPullbackFrames.factoredPullbackFrame, FrameComposition.pullbackGlobalFrame,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  erw [(Scheme.Modules.pullbackComp i f).hom.naturality_assoc φ.hom]
  erw [(Scheme.Modules.pullbackCongr h.symm).hom.naturality_assoc φ.hom]
  erw [(Scheme.Modules.pullbackComp a j).inv.naturality_assoc φ.hom]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareNaturality
