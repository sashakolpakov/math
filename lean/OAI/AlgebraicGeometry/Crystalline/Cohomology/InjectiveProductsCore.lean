import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Injective Products Core -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveProductsCore.InjectiveProducts

noncomputable section

/-! # Products of injective objects remain injective -/

open _root_.CategoryTheory Limits

variable {C : Type*} [Category C] {ι : Type*} (I : ι → C) [HasProduct I] [∀ i, Injective (I i)]

theorem injective : Injective (∏ᶜ I) where
  factors g f _ := by
    choose h hh using fun i => Injective.factors (g ≫ Pi.π I i) f
    refine ⟨Pi.lift h, ?_⟩
    apply Pi.hom_ext
    intro i
    exact (Category.assoc _ _ _).trans ((congrArg (fun a => f ≫ a) (Pi.lift_comp_π h i)).trans (hh i))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveProductsCore.InjectiveProducts
