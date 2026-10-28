import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints

/-! # Product Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.ProductPoints.Construction

noncomputable section

/-! Parameterized group points retain their actual parameter and group
coordinates when expressed on the original product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters

universe u

variable {S : Scheme.{u}} (Q A : Over S) [GrpObj A] (U : Over Q.left)

def parameterProductPoint (x : U ⟶ (Over.pullback Q.hom).obj A) :
    (Over.map Q.hom).obj U ⟶ Q ⊗ A :=
  lift (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U) ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) U).symm x)

theorem parameterProductPoint_fst (x : U ⟶ (Over.pullback Q.hom).obj A) :
    parameterProductPoint Q A U x ≫ fst Q A = CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U := lift_fst _ _

theorem parameterProductPoint_snd (x : U ⟶ (Over.pullback Q.hom).obj A) :
    parameterProductPoint Q A U x ≫ snd Q A = (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) U).symm x :=
  lift_snd _ _

theorem parameterProductPoint_one :
    parameterProductPoint Q A U 1 = lift (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U) (1 : (Over.map Q.hom).obj U ⟶ A) :=
  congrArg (lift (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)) (map_one (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv Q.hom (Grp.mk A) U).symm)

theorem parameterProductPoint_left (x : U ⟶ (Over.pullback Q.hom).obj A) :
    (parameterProductPoint Q A U x).left = x.left ≫ (pullbackSymmetry Q.hom A.hom).inv := by
  apply pullback.hom_ext
  · change (parameterProductPoint Q A U x ≫ fst Q A).left = _
    rw [parameterProductPoint, lift_fst]
    change U.hom = x.left ≫ (pullbackSymmetry Q.hom A.hom).inv ≫ pullback.fst Q.hom A.hom
    rw [pullbackSymmetry_inv_comp_fst]
    exact x.w.symm
  · change (parameterProductPoint Q A U x ≫ snd Q A).left = _
    rw [parameterProductPoint, lift_snd, CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.pullbackPoint_original_left]
    rw [Category.assoc, pullbackSymmetry_inv_comp_snd]

variable {A} {B : Over S} [GrpObj B] (f : A ⟶ B)

theorem parameterProductPoint_comp (x : U ⟶ (Over.pullback Q.hom).obj A) :
    parameterProductPoint Q B U (x ≫ (Over.pullback Q.hom).map f) =
      parameterProductPoint Q A U x ≫ (𝟙 Q ⊗ₘ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [parameterProductPoint, lift_fst, Category.assoc, tensorHom_fst, Category.comp_id]
  · simp only [parameterProductPoint, lift_snd, Category.assoc, tensorHom_snd, lift_snd_assoc]
    exact CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.pullbackPoint_symm_comp Q.hom f U x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.ProductPoints.Construction
