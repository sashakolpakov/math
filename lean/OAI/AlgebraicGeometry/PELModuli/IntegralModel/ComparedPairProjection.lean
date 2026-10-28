import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FunctorPairComparison

/-! # Compared Pair Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComparedPairProjection

noncomputable section

/-! A product projection is unchanged when the two comparison
isomorphisms are expressed through a second native convention. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v w

theorem comparedPairProjection
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {T Z : Scheme.{w}} (F : C ⥤ Over T) [F.Monoidal] (D A : C)
    {D₀ A₀ D₁ A₁ : Over T} (cD : F.obj D ≅ D₀) (cA : F.obj A ≅ A₀)
    (eD : F.obj D ≅ D₁) (eA : F.obj A ≅ A₁)
    (p : (F.obj (D ⊗ A)).left ⟶ Z) (q : (D₀ ⊗ A₀).left ⟶ Z)
    (h : (cD.hom ⊗ₘ cA.hom).left ≫ q =
      (Functor.LaxMonoidal.μ F D A).left ≫ p) :
    ((cD.symm ≪≫ eD).inv ⊗ₘ (cA.symm ≪≫ eA).inv).left ≫ q =
      (FunctorPairComparison.functorPairComparison F D A eD eA).inv.left ≫ p := by
  have ht : (cD.symm ≪≫ eD).inv ⊗ₘ (cA.symm ≪≫ eA).inv =
      (eD.inv ⊗ₘ eA.inv) ≫ (cD.hom ⊗ₘ cA.hom) := by
    simp only [Iso.trans_inv, Iso.symm_inv, tensorHom_comp_tensorHom]
  rw [ht, Over.comp_left, Category.assoc, h, ← Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComparedPairProjection
