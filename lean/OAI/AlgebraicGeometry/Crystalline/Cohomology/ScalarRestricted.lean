import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Scalar Restricted -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestricted.ScalarRestrictedAdditiveMap

noncomputable section

/-! # The underlying additive map of a scalar-restricted module morphism -/

open _root_.CategoryTheory

universe u v

variable {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
  {M : ModuleCat.{v} S} {N : ModuleCat.{v} R}

def map (f : (ModuleCat.restrictScalars φ).obj M ⟶ N) : M →+ N :=
  f.hom.toAddMonoidHom

theorem apply (f : (ModuleCat.restrictScalars φ).obj M ⟶ N) (x : M) :
    ScalarRestrictedAdditiveMap.map φ f x = f.hom x := rfl

theorem triple_comp_apply {M₁ M₂ M₃ : ModuleCat.{v} S} {P : ModuleCat.{v} R}
    (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (h : (ModuleCat.restrictScalars φ).obj M₃ ⟶ P) (x : M₁) :
    ScalarRestrictedAdditiveMap.map φ ((ModuleCat.restrictScalars φ).map (f ≫ g) ≫ h) x = h.hom (g.hom (f.hom x)) := rfl

theorem triple_comp_additive_apply {M₁ M₂ M₃ : ModuleCat.{v} S} {P : ModuleCat.{v} R}
    (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (h : (ModuleCat.restrictScalars φ).obj M₃ ⟶ P) (x : M₁) :
    ScalarRestrictedAdditiveMap.map φ ((ModuleCat.restrictScalars φ).map (f ≫ g) ≫ h) x = ScalarRestrictedAdditiveMap.map φ h (g.hom (f.hom x)) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestricted.ScalarRestrictedAdditiveMap
