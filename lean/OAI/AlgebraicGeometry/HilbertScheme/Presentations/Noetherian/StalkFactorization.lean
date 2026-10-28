import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization
import Mathlib.AlgebraicGeometry.SpreadingOut

/-! # Stalk Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.StalkFactorization

noncomputable section

/-! Factorization of a map from a locally noetherian scheme through a
locally finite type monomorphism is detected on every local spectrum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lift_of_fromSpecStalk {T X Y : Scheme.{u}} [IsLocallyNoetherian T]
    (f : T ⟶ Y) (j : X ⟶ Y) [Mono j] [LocallyOfFiniteType j]
    (h : ∀ t : T, ∃ g : Spec (T.presheaf.stalk t) ⟶ X, g ≫ j = T.fromSpecStalk t ≫ f) :
    ∃! g : T ⟶ X, g ≫ j = f := by
  choose g hg using h
  choose U hU k _ hk using fun t => spread_out_of_isGermInjective' f j (g t) (hg t)
  let C : T.OpenCover.{u} := {
    I₀ := T
    X := fun t => (U t).toScheme
    f := fun t => (U t).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun t => ⟨t, ⟨t, hU t⟩, rfl⟩, inferInstance⟩ }
  exact Local.MorphismFactorization.lift_of_openCover C f j (fun t => ⟨k t, hk t⟩)

theorem over_lift_of_fromSpecStalk {S : Scheme.{u}} {T X Y : Over S}
    [IsLocallyNoetherian T.left] (f : T ⟶ Y) (j : X ⟶ Y)
    [Mono j.left] [LocallyOfFiniteType j.left]
    (h : ∀ t : T.left, ∃ g : Spec (T.left.presheaf.stalk t) ⟶ X.left,
      g ≫ j.left = T.left.fromSpecStalk t ≫ f.left) :
    ∃! g : T ⟶ X, g ≫ j = f := by
  obtain ⟨g, hg, _⟩ := lift_of_fromSpecStalk f.left j.left h
  have hw : g ≫ X.hom = T.hom := by
    rw [← j.w, ← Category.assoc, hg]
    exact f.w
  let g' : T ⟶ X := Over.homMk g hw
  have hg' : g' ≫ j = f := Over.OverMorphism.ext hg
  let : Mono j := Over.mono_of_mono_left j
  exact ⟨g', hg', fun k hk => (cancel_mono j).mp (hk.trans hg'.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.StalkFactorization
