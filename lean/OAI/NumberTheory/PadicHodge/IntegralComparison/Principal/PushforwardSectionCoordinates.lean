import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSection

/-! # Pushforward Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionCoordinates

noncomputable section

/-! Multiplication by the same section before and after passing to
the principal diagram uses the original affine-section coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (ω : Γ(N, f ⁻¹ᵁ U))

local instance nativeSectionModule : Module Γ(X, f ⁻¹ᵁ U)
    ((Affine.ModuleExactSections.sections U).obj (PushforwardSection.target f N)) :=
  inferInstanceAs (Module Γ(X, f ⁻¹ᵁ U) Γ(N, f ⁻¹ᵁ U))

def sectionsMap : (Affine.ModuleExactSections.sections U).obj (PushforwardSection.source f) ⟶
    (Affine.ModuleExactSections.sections U).obj (PushforwardSection.target f N) :=
  ModuleCat.ofHom (X := (Affine.ModuleExactSections.sections U).obj (PushforwardSection.source f))
    (Y := (Affine.ModuleExactSections.sections U).obj (PushforwardSection.target f N))
    { toFun := fun x => (show Γ(X, f ⁻¹ᵁ U) from x) • ω
      map_add' := by
        intro x y
        change Γ(X, f ⁻¹ᵁ U) at x y
        exact add_smul x y ω
      map_smul' := by
        intro a x
        change Γ(X, f ⁻¹ᵁ U) at x
        change (f.app U a * x) • ω = f.app U a • (x • ω)
        exact mul_smul _ _ _ }

theorem atOne_hom :
    ((AtOne.iso U hU).app (PushforwardSection.source f)).hom ≫
      (PushforwardSection.map f U hU N ω).app (op (AtOne.object U)) =
    sectionsMap f U N ω ≫ ((AtOne.iso U hU).app (PushforwardSection.target f N)).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact PushforwardSection.atOne f U hU N ω x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionCoordinates
