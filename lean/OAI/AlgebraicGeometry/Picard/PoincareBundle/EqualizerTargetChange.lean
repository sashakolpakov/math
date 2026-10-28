import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Equalizer Target Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerTargetChange

noncomputable section

/-!
# Changing the target of an invariant diagram by a monomorphism
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category C] [HasEqualizers C]
  {X Y Z : C} (a b : X ⟶ Y) (u : Y ⟶ Z) [Mono u]

/-- Postcomposing the two invariant arrows by a monomorphism retains exactly the same equalizer. -/
def equalizerIso : equalizer (a ≫ u) (b ≫ u) ≅ equalizer a b where
  hom := equalizer.lift (equalizer.ι (a ≫ u) (b ≫ u)) (by
    apply (cancel_mono u).mp
    simpa only [Category.assoc] using equalizer.condition (a ≫ u) (b ≫ u))
  inv := equalizer.lift (equalizer.ι a b) (by
    rw [← Category.assoc, equalizer.condition, Category.assoc])
  hom_inv_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, Category.id_comp]

/-- The target-change isomorphism retains the actual invariant inclusion. -/
theorem hom_ι :
    (equalizerIso a b u).hom ≫ equalizer.ι a b = equalizer.ι (a ≫ u) (b ≫ u) :=
  equalizer.lift_ι _ _

theorem inv_ι :
    (equalizerIso a b u).inv ≫ equalizer.ι (a ≫ u) (b ≫ u) = equalizer.ι a b :=
  equalizer.lift_ι _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerTargetChange
