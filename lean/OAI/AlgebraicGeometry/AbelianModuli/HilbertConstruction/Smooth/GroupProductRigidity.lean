import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProductRigidity
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Product Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GroupProductRigidity

noncomputable section

/-! Maps from proper smooth connected products into a separated group scheme are determined by their restrictions to two pointed axes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K]

theorem smoothGroupProductMap_eq_of_axes (G B H : Over (Spec (.of K)))
    [UniversallyClosed G.hom] [Smooth G.hom] [GeometricallyConnected G.hom]
    [PreconnectedSpace B.left] [IsReduced (G ⊗ B).left]
    [GrpObj H] [IsSeparated H.hom]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) (y : 𝟙_ (Over (Spec (.of K))) ⟶ B)
    (f h : G ⊗ B ⟶ H)
    (hRight : lift (𝟙 G) (toUnit G ≫ y) ≫ f = lift (𝟙 G) (toUnit G ≫ y) ≫ h)
    (hLeft : lift (toUnit B ≫ x) (𝟙 B) ≫ f = lift (toUnit B ≫ x) (𝟙 B) ≫ h) : f = h := by
  let δ : G ⊗ B ⟶ H := f * h⁻¹
  let j : G ⟶ G ⊗ B := lift (𝟙 G) (toUnit G ≫ y)
  let i : B ⟶ G ⊗ B := lift (toUnit B ≫ x) (𝟙 B)
  have hj : j ≫ δ = 1 := by
    change j ≫ (f * h⁻¹) = 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, hRight, mul_inv_cancel]
  have hi : i ≫ δ = 1 := by
    change i ≫ (f * h⁻¹) = 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, hLeft, mul_inv_cancel]
  let : H.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from H.hom]
    infer_instance
  have : IsReduced (pullback G.hom B.hom) := inferInstanceAs (IsReduced (G ⊗ B).left)
  have hδ : δ.left = pullback.snd G.hom B.hom ≫ B.hom ≫ η[H].left :=
    ProductRigidity.smoothProperProductMap_eq_constant_of_axes G.hom B.hom x.left x.w y.left y.w δ.left η[H].left
      (congrArg Over.Hom.left hj) (congrArg Over.Hom.left hi)
  have Hδ : δ = 1 := by
    ext1
    change δ.left = (pullback.fst G.hom B.hom ≫ G.hom) ≫ η[H].left
    rw [pullback.condition]
    exact hδ.trans (Category.assoc _ _ _).symm
  exact mul_inv_eq_one.mp Hδ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GroupProductRigidity
