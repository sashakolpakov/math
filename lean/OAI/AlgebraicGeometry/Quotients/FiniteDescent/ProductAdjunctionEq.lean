import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Product Adjunction Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductAdjunctionEq

noncomputable section

/-! Adjunction transposes of componentwise product maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

namespace Construction.ProductAdjunction

variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
variable {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
variable {I : Type u} (P : I → C) (Q : I → D) [HasProduct P] [HasProduct Q]
variable (f : (∏ᶜ P) ⟶ R.obj (∏ᶜ Q)) (φ : ∀ i, P i ⟶ R.obj (Q i))
variable (h : ∀ i, f ≫ R.map (Pi.π Q i) = Pi.π P i ≫ φ i)

include h

theorem transpose_π (i : I) :
    (a.homEquiv _ _).symm f ≫ Pi.π Q i =
      L.map (Pi.π P i) ≫ (a.homEquiv _ _).symm (φ i) := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  exact h i

variable [HasProduct (fun i => L.obj (P i))]

theorem transpose_eq : (a.homEquiv _ _).symm f =
    piComparison L P ≫ Limits.Pi.map (fun i => (a.homEquiv _ _).symm (φ i)) := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, Pi.map_π, piComparison_comp_π_assoc]
  exact transpose_π a P Q f φ h i

theorem isIso_transpose [HasProductsOfShape I D] [IsIso (piComparison L P)]
    [∀ i, IsIso ((a.homEquiv _ _).symm (φ i))] : IsIso ((a.homEquiv _ _).symm f) := by
  rw [transpose_eq a P Q f φ h]
  infer_instance

end Construction.ProductAdjunction

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductAdjunctionEq
