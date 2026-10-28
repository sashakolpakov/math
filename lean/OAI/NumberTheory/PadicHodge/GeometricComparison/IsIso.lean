import Mathlib.CategoryTheory.Iso

/-! # Is Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IsIso.IsIsoSquare

/-! A typed isomorphism cancellation interface for commuting squares. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] {A B D E : C}
  (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (d : E ⟶ D)

theorem left (h : a ≫ b = c ≫ d) (hb : IsIso b) (hc : IsIso c) (hd : IsIso d) : IsIso a := by
  let := hb
  let := hc
  let := hd
  exact (isIso_comp_right_iff a b).mp (h.symm ▸ (inferInstanceAs (IsIso (c ≫ d))))

end OAI.NumberTheory.PadicHodge.GeometricComparison.IsIso.IsIsoSquare
