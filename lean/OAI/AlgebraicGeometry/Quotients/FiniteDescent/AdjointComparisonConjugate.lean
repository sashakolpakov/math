import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Adjoint Comparison Conjugate -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AdjointComparisonConjugate.Construction.AdjointComparison

/-! A hom-set formula for comparing left adjoints through their right-adjoint mate. -/

open _root_.CategoryTheory

universe v₁ v₂ u₁ u₂

theorem homEquiv_conjugate {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {N : D} (t : L₁.obj M ⟶ N) :
    a₂.homEquiv M N (α.app M ≫ t) =
      a₁.homEquiv M N t ≫ (conjugateEquiv a₁ a₂ α).app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← unit_conjugateEquiv, Category.assoc,
    ← (conjugateEquiv a₁ a₂ α).naturality, ← Category.assoc]

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AdjointComparisonConjugate.Construction.AdjointComparison
