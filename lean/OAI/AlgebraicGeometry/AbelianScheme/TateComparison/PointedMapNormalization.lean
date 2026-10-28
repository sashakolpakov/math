import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Pointed Map Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PointedMapNormalization

noncomputable section

/-! Subtracting a constant map preserves all point differences, on
arbitrary test schemes over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem normalizedMap_point_differences {S : Scheme.{u}} {X A T : Over S}
    [GrpObj A] [IsCommMonObj A] (f : X ⟶ A) (c : 𝟙_ (Over S) ⟶ A)
    (x y : T ⟶ X) :
    (x ≫ (f / (toUnit X ≫ c))) / (y ≫ (f / (toUnit X ≫ c))) = (x ≫ f) / (y ≫ f) := by
  simp only [GrpObj.comp_div, ← Category.assoc, comp_toUnit]
  exact div_div_div_cancel_right _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PointedMapNormalization
