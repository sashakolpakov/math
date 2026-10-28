import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMap

/-! # Descent Cocycle Map Cartesian -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMapCartesian.DescentCocycle

noncomputable section

/-! A cartesian morphism of overlaps remains cartesian on composable
pairs. This preserves the geometric family used for normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B T X Y : C} (u : T ⟶ B) (a : X ⟶ T) (b : Y ⟶ T)
    (p : X ⟶ Y) (hp : p ≫ b = a)
    (t : DescentCocycleChange.DescentCocycle.overlap u a ⟶ X) (v : DescentCocycleChange.DescentCocycle.overlap u b ⟶ Y)
    (htransport : t ≫ p = DescentCocycleMap.DescentCocycle.map u a b p hp ≫ v)

theorem mapComposition_cartesian
    (hs : IsPullback (DescentCocycleChange.DescentCocycle.source u a) (DescentCocycleMap.DescentCocycle.map u a b p hp) p (DescentCocycleChange.DescentCocycle.source u b)) :
    IsPullback (pullback.fst t (DescentCocycleChange.DescentCocycle.source u a)) (DescentCocycleMap.DescentCocycle.mapComposition u a b p hp t v htransport)
      (DescentCocycleMap.DescentCocycle.map u a b p hp) (pullback.fst v (DescentCocycleChange.DescentCocycle.source u b)) := by
  have ho := (IsPullback.of_hasPullback t (DescentCocycleChange.DescentCocycle.source u a)).flip.paste_horiz hs.flip
  have ho' : IsPullback
      (DescentCocycleMap.DescentCocycle.mapComposition u a b p hp t v htransport ≫ pullback.snd v (DescentCocycleChange.DescentCocycle.source u b))
      (pullback.fst t (DescentCocycleChange.DescentCocycle.source u a)) (DescentCocycleChange.DescentCocycle.source u b) (DescentCocycleMap.DescentCocycle.map u a b p hp ≫ v) := by
    simpa only [DescentCocycleMap.DescentCocycle.mapComposition, pullback.lift_snd, htransport] using ho
  exact (ho'.of_right (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback v (DescentCocycleChange.DescentCocycle.source u b)).flip).flip

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMapCartesian.DescentCocycle
