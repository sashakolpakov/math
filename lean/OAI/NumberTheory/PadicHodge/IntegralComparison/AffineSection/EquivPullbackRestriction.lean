import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivRestriction

/-! # Equiv Pullback Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivPullbackRestriction.Geometry

noncomputable section

/-! Pull back and restrict a parameter through the same specified
original affine equivalence, retaining the literal target restrictions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X₁ X₂ : Over (Spec (CommRingCat.of R))) (f : X₁ ⟶ X₂)
  (U₁ : X₁.left.Opens) (U₂ U₀ : X₂.left.Opens)
  (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
  (e : EquivGeometry.ring R X₁ U₁ ≃ₐ[R] EquivGeometry.ring R X₂ U₂)
  (hpull : U₁ ≤ f.left ⁻¹ᵁ U₀)
  (V : X₁.left.Opens) (hVU : V ≤ U₁)
  (W : X₂.left.Opens) (hW₀ : W ≤ U₀) (hW₂ : W ≤ U₂)
  (hVW : V ≤ f.left ⁻¹ᵁ W)
  (hTW : EquivGeometry.targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V ≤ W)

theorem pullback_restriction (a : EquivGeometry.ring R X₂ U₀) :
    EquivGeometry.sectionEquiv R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hVU
      (f.left.appLE W V hVW (X₂.left.presheaf.map (homOfLE hW₀).op a)) =
    X₂.left.presheaf.map (homOfLE hTW).op
      (X₂.left.presheaf.map (homOfLE hW₂).op
        (e (f.left.appLE U₀ U₁ hpull a))) := by
  have hleft := ConcreteCategory.congr_hom
    (f.left.map_appLE hVW (homOfLE hW₀).op) a
  have hright := ConcreteCategory.congr_hom
    (f.left.appLE_map hpull (homOfLE hVU).op) a
  have hin : f.left.appLE W V hVW (X₂.left.presheaf.map (homOfLE hW₀).op a) =
      X₁.left.presheaf.map (homOfLE hVU).op (f.left.appLE U₀ U₁ hpull a) :=
    hleft.trans hright.symm
  rw [hin, EquivRestriction.Geometry.sectionEquiv_restriction]
  have hr : X₂.left.presheaf.map
      (homOfLE (EquivGeometry.target_below R X₁ X₂ U₁ U₂ hU₁ hU₂ e V)).op =
      X₂.left.presheaf.map (homOfLE hW₂).op ≫ X₂.left.presheaf.map (homOfLE hTW).op := by
    rw [← Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hr (e (f.left.appLE U₀ U₁ hpull a))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivPullbackRestriction.Geometry
