import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

/-! # Pull Hom -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom

noncomputable section

/-!
# Native geometric formulas for pullback of descent morphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open Pseudofunctor.LocallyDiscreteOpToCat

/-- Pulling a descent morphism uses the standard sheaf pullback composition isomorphisms. -/
theorem pullHom_eq {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := KernelLinearization.modulePullbacks) a g gf₁ gf₂ h₁ h₂ =
      (Scheme.Modules.pullbackComp g f₁ ≪≫ Scheme.Modules.pullbackCongr h₁).inv.app L₁ ≫
        (Scheme.Modules.pullback g).map a ≫
          (Scheme.Modules.pullbackComp g f₂ ≪≫ Scheme.Modules.pullbackCongr h₂).hom.app L₂ := by
  subst gf₁
  subst gf₂
  simp only [pullHom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.trans_refl]
  rfl

/-- The geometric pullback formula, kept as a named proposition for stable specialization. -/
def HasPullHomFormula {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) : Prop :=
  pullHom (F := KernelLinearization.modulePullbacks) a g gf₁ gf₂ h₁ h₂ =
    (Scheme.Modules.pullbackComp g f₁ ≪≫ Scheme.Modules.pullbackCongr h₁).inv.app L₁ ≫
      (Scheme.Modules.pullback g).map a ≫
        (Scheme.Modules.pullbackComp g f₂ ≪≫ Scheme.Modules.pullbackCongr h₂).hom.app L₂

/-- The standard formula holds for all geometric descent morphisms. -/
theorem hasPullHomFormula {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    HasPullHomFormula a g gf₁ gf₂ h₁ h₂ := pullHom_eq a g gf₁ gf₂ h₁ h₂

/-- The native descent pullback has the standard formula for the affine coordinate maps. -/
theorem affine_hasPullHomFormula {R S T : CommRingCat.{u}} {L : (Spec R).Modules}
    (f g : R ⟶ S) (k : S ⟶ T)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    HasPullHomFormula a (Spec.map k) (Spec.map (f ≫ k)) (Spec.map (g ≫ k))
      (Spec.map_comp f k).symm (Spec.map_comp g k).symm :=
  hasPullHomFormula (X₁ := Spec R) (X₂ := Spec R) (Y := Spec S) (Y' := Spec T)
    (L₁ := L) (L₂ := L) (f₁ := Spec.map f) (f₂ := Spec.map g)
    a (Spec.map k) (Spec.map (f ≫ k)) (Spec.map (g ≫ k))
    (Spec.map_comp f k).symm (Spec.map_comp g k).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom
