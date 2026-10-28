import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Equalizer Congr -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerCongr

noncomputable section

/-!
# Equality transport of an equalizer retains its actual inclusion
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category C] [HasEqualizers C]
  {X Y : C} {a b c d : X ⟶ Y}

def iso (ha : a = c) (hb : b = d) : equalizer a b ≅ equalizer c d :=
  eqToIso (congrArg₂ (fun f g : X ⟶ Y => equalizer f g) ha hb)

theorem hom_ι (ha : a = c) (hb : b = d) :
    (iso ha hb).hom ≫ equalizer.ι c d = equalizer.ι a b := by
  subst c
  subst d
  exact Category.id_comp _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualizerCongr
