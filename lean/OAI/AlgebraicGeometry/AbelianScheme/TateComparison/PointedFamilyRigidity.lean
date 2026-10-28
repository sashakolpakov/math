import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity

/-! # Pointed Family Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PointedFamilyRigidity

noncomputable section

/-! A pointed family of maps from a proper variety to a group scheme is
constant in an integral parameter space. This is the geometric rigidity
step used when spreading maps to a finite coefficient field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (Y X Z : Over (Spec (.of k))) [GrpObj X] [GrpObj Z]
  [LocallyOfFiniteType Y.hom] [IsProper X.hom]
  [LocallyOfFiniteType Z.hom] [IsSeparated Z.hom] [IsIntegral (Y ⊗ X).left]

theorem pointedFamily_eq_constant
    (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (f : Y ⊗ X ⟶ Z) (g : X ⟶ Z) [IsMonHom g]
    (hf : lift (𝟙 Y) (toUnit Y ≫ η[X]) ≫ f = 1)
    (hg : lift (toUnit X ≫ y₀) (𝟙 X) ≫ f = g) : f = snd Y X ≫ g := by
  let d := f / (snd Y X ≫ g)
  have hd : lift (toUnit X ≫ y₀) (𝟙 X) ≫ d = toUnit X ≫ η[Z] := by
    simp only [d, GrpObj.comp_div, ← Category.assoc, lift_snd, Category.id_comp, hg,
      div_self']
    rfl
  have hr := ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity.Construction.rigidity_of_constant_fiber Y X Z y₀ η[X] η[Z] d hd
  have hz : lift (𝟙 Y) (toUnit Y ≫ η[X]) ≫ d = 1 := by
    simp only [d, GrpObj.comp_div, ← Category.assoc, lift_snd, hf]
    change 1 / ((1 : Y ⟶ X) ≫ g) = 1
    rw [MonObj.one_comp, div_self']
  rw [hz, MonObj.comp_one] at hr
  exact div_eq_one.mp hr

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PointedFamilyRigidity
