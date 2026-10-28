import OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedHomIsoNormalization

/-! # Ext Small Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExtSmallComparison

noncomputable section

/-! # The Ext comparison uses the same small localized morphism -/

open _root_.CategoryTheory Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C] [HasExt.{w} C]

theorem extSmallShiftedHom_normalization {A B : C} (n : ℕ) (a : Ext A B n) :
    Ext.homAddEquiv a =
      Localization.SmallShiftedHom.equiv (HomologicalComplex.quasiIso C ℤᵘᵖ)
        DerivedCategory.Q a := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExtSmallComparison
