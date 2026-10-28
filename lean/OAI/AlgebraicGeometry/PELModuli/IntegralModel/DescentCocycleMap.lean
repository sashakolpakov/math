import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange

/-! # Descent Cocycle Map -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMap.DescentCocycle

noncomputable section

/-! Functoriality of the actual overlap, its diagonal, and its composition.
These equations allow componentwise transport laws to be assembled. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B T X Y : C} (u : T ⟶ B) (a : X ⟶ T) (b : Y ⟶ T)
    (p : X ⟶ Y) (hp : p ≫ b = a)

def map : DescentCocycleChange.DescentCocycle.overlap u a ⟶ DescentCocycleChange.DescentCocycle.overlap u b :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source u a ≫ p) (DescentCocycleChange.DescentCocycle.base u a) (by
    rw [Category.assoc, ← Category.assoc p, hp]
    exact DescentCocycleChange.DescentCocycle.source_condition u a)

@[reassoc (attr := simp)] theorem map_source : map u a b p hp ≫ DescentCocycleChange.DescentCocycle.source u b = DescentCocycleChange.DescentCocycle.source u a ≫ p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem map_base : map u a b p hp ≫ DescentCocycleChange.DescentCocycle.base u b = DescentCocycleChange.DescentCocycle.base u a :=
  pullback.lift_snd _ _ _

theorem diagonal_map : DescentCocycleChange.DescentCocycle.diagonal u a ≫ map u a b p hp = p ≫ DescentCocycleChange.DescentCocycle.diagonal u b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, map_source, DescentCocycleChange.DescentCocycle.diagonal_source_assoc, DescentCocycleChange.DescentCocycle.diagonal_source, Category.comp_id]
  · simp only [Category.assoc, map_base, DescentCocycleChange.DescentCocycle.diagonal_base, hp]

variable (t : DescentCocycleChange.DescentCocycle.overlap u a ⟶ X) (v : DescentCocycleChange.DescentCocycle.overlap u b ⟶ Y)
    (ht : t ≫ a = DescentCocycleChange.DescentCocycle.base u a) (hv : v ≫ b = DescentCocycleChange.DescentCocycle.base u b)
    (htransport : t ≫ p = map u a b p hp ≫ v)

def mapComposition : pullback t (DescentCocycleChange.DescentCocycle.source u a) ⟶ pullback v (DescentCocycleChange.DescentCocycle.source u b) :=
  pullback.lift (pullback.fst t (DescentCocycleChange.DescentCocycle.source u a) ≫ map u a b p hp)
    (pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ map u a b p hp) (by
      rw [Category.assoc, ← htransport, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, map_source])

theorem composition_map :
    DescentCocycleChange.DescentCocycle.composition u a t ht ≫ map u a b p hp =
      mapComposition u a b p hp t v htransport ≫ DescentCocycleChange.DescentCocycle.composition u b v hv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, map_source, DescentCocycleChange.DescentCocycle.composition_source_assoc,
      DescentCocycleChange.DescentCocycle.composition_source, mapComposition, pullback.lift_fst_assoc]
  · simp only [Category.assoc, map_base, DescentCocycleChange.DescentCocycle.composition_base, mapComposition,
      pullback.lift_snd_assoc]

include htransport in
theorem normalized_component (hn : DescentCocycleChange.DescentCocycle.diagonal u b ≫ v = 𝟙 Y) :
    (DescentCocycleChange.DescentCocycle.diagonal u a ≫ t) ≫ p = p := by
  rw [Category.assoc, htransport, ← Category.assoc, diagonal_map,
    Category.assoc, hn, Category.comp_id]

include htransport in
theorem cocycle_component
    (hc : DescentCocycleChange.DescentCocycle.composition u b v hv ≫ v = pullback.snd v (DescentCocycleChange.DescentCocycle.source u b) ≫ v) :
    (DescentCocycleChange.DescentCocycle.composition u a t ht ≫ t) ≫ p = (pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ t) ≫ p := by
  rw [Category.assoc, htransport, ← Category.assoc, composition_map u a b p hp t v ht hv htransport,
    Category.assoc, hc]
  simp only [mapComposition, pullback.lift_snd_assoc, Category.assoc, htransport]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMap.DescentCocycle
