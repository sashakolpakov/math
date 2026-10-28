/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/Picard/UnitPullback.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOne

/-! # Unit Scalar -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitScalar

noncomputable section

/-! Scalar maps on the actual structure module. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

def unitEndomorphismOfTopSection {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    Invertible.Scheme.Modules.unitObj X ⟶ Invertible.Scheme.Modules.unitObj X :=
  AffineRankOne.globalGeneratorHom (Invertible.Scheme.Modules.unitObj X) r

@[simp]
theorem unitEndomorphismOfTopSection_app_apply {X : Scheme.{u}}
    (r : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (unitEndomorphismOfTopSection r).val.app (op U) a =
      a * X.presheaf.map U.leTop.op r := rfl

theorem unitEndomorphismOfTopSection_comp {X : Scheme.{u}} (r s : Γ(X, ⊤)) :
    unitEndomorphismOfTopSection r ≫ unitEndomorphismOfTopSection s =
      unitEndomorphismOfTopSection (r * s) := by
  apply _root_.SheafOfModules.hom_ext
  ext U
  change (1 * X.presheaf.map U.unop.leTop.op r) *
      X.presheaf.map U.unop.leTop.op s =
    1 * X.presheaf.map U.unop.leTop.op (r * s)
  rw [map_mul, mul_assoc]

@[simp]
theorem unitEndomorphismOfTopSection_one {X : Scheme.{u}} :
    unitEndomorphismOfTopSection (1 : Γ(X, ⊤)) = 𝟙 (Invertible.Scheme.Modules.unitObj X) := by
  apply _root_.SheafOfModules.hom_ext
  ext U
  change 1 * X.presheaf.map U.unop.leTop.op 1 = 1
  rw [map_one, mul_one]

def unitAutomorphismOfTopUnit {X : Scheme.{u}} (r : Γ(X, ⊤)ˣ) :
    Invertible.Scheme.Modules.unitObj X ≅ Invertible.Scheme.Modules.unitObj X where
  hom := unitEndomorphismOfTopSection (r : Γ(X, ⊤))
  inv := unitEndomorphismOfTopSection (↑r⁻¹ : Γ(X, ⊤))
  hom_inv_id := by rw [unitEndomorphismOfTopSection_comp, r.mul_inv,
    unitEndomorphismOfTopSection_one]
  inv_hom_id := by rw [unitEndomorphismOfTopSection_comp, r.inv_mul,
    unitEndomorphismOfTopSection_one]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitScalar
