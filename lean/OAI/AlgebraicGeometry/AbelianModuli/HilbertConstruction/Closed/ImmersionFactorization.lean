import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIdeals

/-! # Immersion Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ImmersionFactorization

noncomputable section

/-! The defining ideal of a closed immersion detects its unique factorization property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem closedImmersion_ideal_factorization {S : Scheme.{u}} {Z M T : Over S}
    (j : Z ⟶ M) [IsClosedImmersion j.left] (f : T ⟶ M) :
    j.left.ker.comap f.left = ⊥ ↔ ∃! g : T ⟶ Z, g ≫ j = f := by
  rw [ConditionIdeals.ideal_comap_eq_bot_iff]
  constructor
  · intro h
    let l := IsClosedImmersion.lift j.left f.left h
    have hl : l ≫ j.left = f.left := IsClosedImmersion.lift_fac _ _ h
    let g : T ⟶ Z := Over.homMk l (by
      rw [← j.w, ← Category.assoc, hl]
      exact f.w)
    have hg : g ≫ j = f := Over.OverMorphism.ext hl
    have : Mono j := Over.mono_of_mono_left j
    exact ⟨g, hg, fun g' hg' => (cancel_mono j).mp (hg'.trans hg.symm)⟩
  · rintro ⟨g, hg, _⟩
    have hleft : g.left ≫ j.left = f.left := congrArg Over.Hom.left hg
    rw [← hleft]
    exact Scheme.Hom.le_ker_comp _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ImmersionFactorization
