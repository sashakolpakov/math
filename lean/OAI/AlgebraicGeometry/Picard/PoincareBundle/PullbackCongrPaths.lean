import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pullback Congr Paths -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackCongrPaths

noncomputable section

/-!
# Normalization of geometric pullback equality paths
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Equality transport along a reflexive scheme equation is the identity. -/
theorem pullbackCongr_refl (f : X ⟶ Y) :
    Scheme.Modules.pullbackCongr (rfl : f = f) = Iso.refl _ := rfl

/-- Normalize the coordinate equality paths around two geometric composition comparisons. -/
theorem normalize {f₁ f₂ f₃ f₄ : X ⟶ Y}
    (h₁ : f₁ = f₂) (h₂ : f₂ = f₃) (h₃ : f₄ = f₃)
    {F G : Y.Modules ⥤ X.Modules}
    (a : F ≅ Scheme.Modules.pullback f₁) (b : G ≅ Scheme.Modules.pullback f₄) :
    (a ≪≫ Scheme.Modules.pullbackCongr h₁) ≪≫
        Scheme.Modules.pullbackCongr h₂ ≪≫ (b ≪≫ Scheme.Modules.pullbackCongr h₃).symm =
      a ≪≫ Scheme.Modules.pullbackCongr (h₁.trans (h₂.trans h₃.symm)) ≪≫ b.symm := by
  subst f₂
  subst f₃
  subst f₄
  simp only [pullbackCongr_refl, Iso.trans_refl, Iso.refl_trans]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackCongrPaths
