import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.FactorizationCriterion

/-! # Equalizer Ideal Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EqualizerIdealCriterion

noncomputable section

/-! Equality of actual morphisms into a separated scheme is detected by
the ideal sheaf of their actual equalizer. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {M Y T : Over S} [IsSeparated Y.hom]

theorem equalizer_ideal_comap_eq_bot_iff (f g : M ⟶ Y) (x : T ⟶ M) :
    (equalizer.ι f g).left.ker.comap x.left = ⊥ ↔ x ≫ f = x ≫ g := by
  rw [← Closed.FactorizationCriterion.over_closed_factorization_iff_comap_bot (equalizer.ι f g) x]
  constructor
  · rintro ⟨y, rfl, _⟩
    rw [Category.assoc, Category.assoc, equalizer.condition]
  · intro h
    refine ⟨equalizer.lift x h, equalizer.lift_ι _ _, ?_⟩
    intro y hy
    apply (cancel_mono (equalizer.ι f g)).mp
    exact hy.trans (equalizer.lift_ι x h).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EqualizerIdealCriterion
