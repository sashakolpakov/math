import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointTransportNaturality

/-! # Iso Four Squares -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoFourSquares.Construction

/-! Four commuting isomorphism squares compose without changing their
actual endpoint comparisons. -/

open _root_.CategoryTheory

theorem iso_functor_four_squares {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A₀ A₁ A₂ A₃ A₄ : C} {B₀ B₁ B₂ B₃ B₄ : D}
    (e₀ : A₀ ≅ A₁) (e₁ : A₁ ≅ A₂) (e₂ : A₂ ≅ A₃) (e₃ : A₃ ≅ A₄)
    (d₀ : B₀ ≅ B₁) (d₁ : B₁ ≅ B₂) (d₂ : B₂ ≅ B₃) (d₃ : B₃ ≅ B₄)
    (a₀ : F.obj A₀ ≅ B₀) (a₁ : F.obj A₁ ≅ B₁) (a₂ : F.obj A₂ ≅ B₂)
    (a₃ : F.obj A₃ ≅ B₃) (a₄ : F.obj A₄ ≅ B₄)
    (h₀ : F.mapIso e₀ ≪≫ a₁ = a₀ ≪≫ d₀) (h₁ : F.mapIso e₁ ≪≫ a₂ = a₁ ≪≫ d₁)
    (h₂ : F.mapIso e₂ ≪≫ a₃ = a₂ ≪≫ d₂) (h₃ : F.mapIso e₃ ≪≫ a₄ = a₃ ≪≫ d₃) :
    F.mapIso (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃) ≪≫ a₄ = a₀ ≪≫ (d₀ ≪≫ d₁ ≪≫ d₂ ≪≫ d₃) :=
  FiberPointTransportNaturality.Construction.iso_functor_square_comp F e₀ (e₁ ≪≫ e₂ ≪≫ e₃) d₀ (d₁ ≪≫ d₂ ≪≫ d₃) a₀ a₁ a₄ h₀
    (FiberPointTransportNaturality.Construction.iso_functor_square_comp F e₁ (e₂ ≪≫ e₃) d₁ (d₂ ≪≫ d₃) a₁ a₂ a₄ h₁
      (FiberPointTransportNaturality.Construction.iso_functor_square_comp F e₂ e₃ d₂ d₃ a₂ a₃ a₄ h₂ h₃))

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoFourSquares.Construction
