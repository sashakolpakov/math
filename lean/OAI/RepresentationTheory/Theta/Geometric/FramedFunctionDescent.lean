import OAI.RepresentationTheory.Theta.Geometric.RegularFunctionDescent
import OAI.RepresentationTheory.Theta.Geometric.DominantLinePullback

/-! # Framed Function Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.FramedFunctionDescent

noncomputable section

/-! Compatible native line-bundle isomorphisms descend in frames once
their regular coefficients descend. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent

variable {X Y : Scheme} (f : X ⟶ Y) (hi : Function.Injective f.appTop)
    (hf : RegularFunctionDescent.HasRegularFunctionDescent f) {M N : Y.Modules}
    (eM : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) (eN : N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)

include hi hf eM eN in
theorem existsUnique_framedHom_of_function_descent
    (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (ha : AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.CompatibleHom f a) :
    ∃! b : M ⟶ N, (Scheme.Modules.pullback f).map b = a := by
  let r := AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedCoefficient (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eM) (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eN) a
  have hr : ∀ {Z : Scheme} (x y : Z ⟶ X), x ≫ f = y ≫ f → x.appTop r = y.appTop r := by
    intro Z x y hxy
    have h := congrArg (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedCoefficient (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame (x ≫ f) eM)
      (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame (x ≫ f) eN)) (ha x y (x ≫ f) rfl hxy.symm)
    rw [AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback.framedCoefficient_pullbackHomTo, AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback.framedCoefficient_pullbackHomTo] at h
    exact h
  obtain ⟨s, hs⟩ := hf r hr
  refine ⟨AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedHom eM eN s, ?_, ?_⟩
  · change (Scheme.Modules.pullback f).map (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedHom eM eN s) = a
    rw [AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedHom_pullback, hs]
    exact AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedHom_coefficient (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eM) (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eN) a
  · intro b hb
    apply DominantLinePullback.IntrinsicDominantPullback.framedPullback_injective_of_appTop f hi eM eN
    dsimp only
    rw [hb, AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedHom_pullback, hs]
    exact (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.framedHom_coefficient (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eM) (AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom.pullbackFrame f eN) a).symm

include hi hf eM eN in
theorem existsUnique_framedIso_of_function_descent
    (a : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (ha : AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.CompatibleHom f a.hom) :
    ∃! b : M ≅ N, (Scheme.Modules.pullback f).mapIso b = a := by
  obtain ⟨b, hb, hu⟩ := existsUnique_framedHom_of_function_descent f hi hf eM eN a.hom ha
  obtain ⟨c, hc, _⟩ := existsUnique_framedHom_of_function_descent f hi hf eN eM a.inv
    (AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.compatibleHom_inverse f a ha)
  have hbc : b ≫ c = 𝟙 M := by
    apply DominantLinePullback.IntrinsicDominantPullback.framedPullback_injective_of_appTop f hi eM eM
    dsimp only
    rw [CategoryTheory.Functor.map_comp, hb, hc, a.hom_inv_id, CategoryTheory.Functor.map_id]
  have hcb : c ≫ b = 𝟙 N := by
    apply DominantLinePullback.IntrinsicDominantPullback.framedPullback_injective_of_appTop f hi eN eN
    dsimp only
    rw [CategoryTheory.Functor.map_comp, hc, hb, a.inv_hom_id, CategoryTheory.Functor.map_id]
  refine ⟨⟨b, c, hbc, hcb⟩, Iso.ext hb, ?_⟩
  intro d hd
  exact Iso.ext (hu d.hom (congrArg Iso.hom hd))

end

end OAI.RepresentationTheory.Theta.Geometric.FramedFunctionDescent
