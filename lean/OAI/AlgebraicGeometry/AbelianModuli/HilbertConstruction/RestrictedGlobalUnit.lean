import Mathlib.AlgebraicGeometry.Scheme

/-! # Restricted Global Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedGlobalUnit

noncomputable section

/-! Restrict a unit of global functions compatibly to every open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def restrictedGlobalUnit {X : Scheme.{u}} (u : Γ(X, ⊤)ˣ) (U : X.Opens) : Γ(X, U)ˣ :=
  Units.map (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.toMonoidHom u

theorem restrictedGlobalUnit_restrict {X : Scheme.{u}} (u : Γ(X, ⊤)ˣ)
    {U V : X.Opens} (h : V ≤ U) :
    Units.map (X.presheaf.map (homOfLE h).op).hom (restrictedGlobalUnit u U) =
      restrictedGlobalUnit u V := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) (u : Γ(X, ⊤))) = _
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ X.presheaf.map (homOfLE h).op) (u : Γ(X, ⊤)) = _
  rw [← X.presheaf.map_comp]
  rfl

theorem restrictedGlobalUnit_val {X : Scheme.{u}} (u : Γ(X, ⊤)ˣ) {n : ℕ}
    (hu : (u : Γ(X, ⊤)) = n) (U : X.Opens) : (restrictedGlobalUnit u U : Γ(X, U)) = n := by
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) (u : Γ(X, ⊤)) = n
  rw [hu, map_natCast]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedGlobalUnit
