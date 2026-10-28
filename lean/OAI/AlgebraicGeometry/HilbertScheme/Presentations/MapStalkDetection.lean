import Mathlib.AlgebraicGeometry.SpreadingOut

/-! # Map Stalk Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MapStalkDetection

noncomputable section

/-! Maps from a locally noetherian scheme are detected on its actual
local spectra. The proof spreads stalkwise equalities to an open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem schemeHom_eq_of_fromSpecStalk {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f g : X ⟶ Y) (h : ∀ x : X, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  choose U hU he using fun x => spread_out_unique_of_isGermInjective' f g (h x)
  let C : X.OpenCover.{u} := {
    I₀ := X
    X := fun x => (U x).toScheme
    f := fun x => (U x).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, ⟨x, hU x⟩, rfl⟩, inferInstance⟩ }
  exact C.hom_ext f g he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MapStalkDetection
