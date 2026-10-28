import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelNaturality
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Coalgebra Map Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoalgebraMapCoordinates

noncomputable section

/-!
# Coordinates of the actual extension/restriction comonad on morphisms
-/

open _root_.CategoryTheory _root_.ModuleCat

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  {M N : ModuleCat.{u} S}

/-- The actual comonad map is the base-ring tensor map on underlying modules. -/
theorem map_apply (a : M ⟶ N) (z : (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj M) :
    letI := f.toAlgebra
    (extendRestrictScalarsAdj.{u,u,u} f).toComonad.map a z =
      Cech.ModelNaturality.tensorMap R S a z := rfl

/-- The categorical coaction compatibility equation has the expected tensor-coordinate form. -/
theorem compatibility_apply
    (α : M ⟶ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj M)
    (β : N ⟶ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj N)
    (a : M ⟶ N)
    (h : α ≫ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.map a = a ≫ β) (m : M) :
    letI := f.toAlgebra
    Cech.ModelNaturality.tensorMap R S a (α m) = β (a m) := by
  let := f.toAlgebra
  have hp := ConcreteCategory.congr_hom h m
  change (extendRestrictScalarsAdj.{u,u,u} f).toComonad.map a (α m) = β (a m) at hp
  rw [map_apply] at hp
  exact hp

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoalgebraMapCoordinates
