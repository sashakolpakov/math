/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCech.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Linear

/-! # Product Forget -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ProductForget

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
universe u

abbrev moduleForget (R : Type u) [Ring R] :=
  forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

def discreteModuleForgetIso
    (R : Type u) [Ring R] {I : Type u} (P : I → ModuleCat.{u} R) :
    Discrete.functor P ⋙ moduleForget R ≅
      Discrete.functor (fun i => (moduleForget R).obj (P i)) :=
  Discrete.natIso fun x => eqToIso (show
    (Discrete.functor P ⋙ moduleForget R).obj x =
      (Discrete.functor fun i => (moduleForget R).obj (P i)).obj x
    from rfl)

theorem discreteModuleForgetIso_comp_hom_app
    (R : Type u) [Ring R] {I : Type u} (P : I → ModuleCat.{u} R)
    (i : I) :
    (moduleForget R).map (Pi.π P i) ≫
        (discreteModuleForgetIso R P).hom.app (Discrete.mk i) =
      (moduleForget R).map (Pi.π P i) := by
  rfl

/-- Forgetting the module structure commutes with products. -/
noncomputable def modulePiForgetIso
    (R : Type u) [Ring R] {I : Type u} (P : I → ModuleCat.{u} R) :
    (moduleForget R).obj (∏ᶜ P) ≅
      ∏ᶜ fun i => (moduleForget R).obj (P i) :=
  preservesLimitIso (moduleForget R) (Discrete.functor P) ≪≫
    HasLimit.isoOfNatIso (discreteModuleForgetIso R P)

/-- The comparison from a forgotten module product to the additive product
commutes with every product projection. -/
@[reassoc]
theorem modulePiForgetIso_hom_π
    (R : Type u) [Ring R] {I : Type u}
    (P : I → ModuleCat.{u} R) (i : I) :
    (modulePiForgetIso R P).hom ≫
        Pi.π (fun i => (moduleForget R).obj (P i)) i =
      (moduleForget R).map
        (Pi.π P i) := by
  dsimp only [modulePiForgetIso]
  rw [Iso.trans_hom]
  change (preservesLimitIso (moduleForget R) (Discrete.functor P)).hom ≫
      ((HasLimit.isoOfNatIso (discreteModuleForgetIso R P)).hom ≫
        limit.π (Discrete.functor fun i => (moduleForget R).obj (P i))
          (Discrete.mk i)) = _
  rw [
    HasLimit.isoOfNatIso_hom_π
      (discreteModuleForgetIso R P) (Discrete.mk i)]
  rw [preservesLimitIso_hom_π_assoc]
  exact discreteModuleForgetIso_comp_hom_app R P i

theorem modulePiForgetIso_naturality
    (R : Type u) [Ring R] {I J : Type u}
    (P : I → ModuleCat.{u} R) (Q : J → ModuleCat.{u} R)
    (f : J → I) (φ : ∀ j, P (f j) ⟶ Q j) :
    (moduleForget R).map
          (Pi.lift fun j => Pi.π P (f j) ≫ φ j) ≫
        (modulePiForgetIso R Q).hom =
      (modulePiForgetIso R P).hom ≫
        Pi.lift (fun j =>
          Pi.π (fun i => (moduleForget R).obj (P i)) (f j) ≫
            (moduleForget R).map (φ j)) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, modulePiForgetIso_hom_π,
    Pi.lift_comp_π, ← Functor.map_comp]
  rw [modulePiForgetIso_hom_π_assoc, ← Functor.map_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ProductForget
