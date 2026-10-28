import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeMap

/-! # Base Change Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeNaturality

noncomputable section

/-! The unique geometric base-change maps preserve every compatible family morphism between Cartesian models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem cartesianBaseChangeMap_natural
    {S T U : Scheme.{u}} (f : T ⟶ U) (c : U ⟶ S)
    {A B : Over S} {X₁ X₂ : Over T} {Y₁ Y₂ : Over U}
    (qX₁ : X₁.left ⟶ A.left) (qY₁ : Y₁.left ⟶ A.left)
    (qX₂ : X₂.left ⟶ B.left) (qY₂ : Y₂.left ⟶ B.left)
    (hX₁ : IsPullback qX₁ X₁.hom A.hom (f ≫ c)) (hY₁ : IsPullback qY₁ Y₁.hom A.hom c)
    (hX₂ : IsPullback qX₂ X₂.hom B.hom (f ≫ c)) (hY₂ : IsPullback qY₂ Y₂.hom B.hom c)
    (i : X₁ ⟶ X₂) (j : Y₁ ⟶ Y₂) (k : A ⟶ B)
    (hT : qX₁ ≫ k.left = i.left ≫ qX₂) (hU : qY₁ ≫ k.left = j.left ≫ qY₂) :
    BaseChangeMap.cartesianBaseChangeMap f c qX₁ qY₁ hX₁ hY₁ ≫ j.left =
      i.left ≫ BaseChangeMap.cartesianBaseChangeMap f c qX₂ qY₂ hX₂ hY₂ := by
  apply hY₂.hom_ext
  · rw [Category.assoc, ← hU, ← Category.assoc, BaseChangeMap.cartesianBaseChangeMap_comp,
      Category.assoc, BaseChangeMap.cartesianBaseChangeMap_comp]
    exact hT
  · rw [Category.assoc, j.w, BaseChangeMap.cartesianBaseChangeMap_over, Category.assoc,
      BaseChangeMap.cartesianBaseChangeMap_over, ← Category.assoc, i.w]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeNaturality
