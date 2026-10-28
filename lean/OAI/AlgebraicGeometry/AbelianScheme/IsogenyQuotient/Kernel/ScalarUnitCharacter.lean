import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.KernelScalar

/-! # Scalar Unit Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.ScalarUnitCharacter.Construction

noncomputable section

/-! A source-independent scalar cocycle gives an actual natural
unit-valued kernel character on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  {f : A ⟶ B} [IsMonHom f]
  [IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) A).left.appTop] (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f)

set_option backward.isDefEq.respectTransparency false in
def kernelScalarUnitCharacter (T : Over S) : (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ where
  toFun z := Units.map z.left.appTop.hom D.kernelScalar_isUnit.unit
  map_one' := by
    apply Units.ext
    simp only [Units.coe_map, IsUnit.unit_spec, Units.val_one]
    change (1 : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left.appTop D.kernelScalar = 1
    exact Relative.KernelScalar.Construction.kernelScalar_one_of_projection_functions D T
  map_mul' z w := by
    apply Units.ext
    simp only [Units.coe_map, IsUnit.unit_spec, Units.val_mul]
    change (z * w).left.appTop D.kernelScalar = z.left.appTop D.kernelScalar * w.left.appTop D.kernelScalar
    exact Relative.KernelScalar.Construction.kernelScalar_mul_of_projection_functions D z w

theorem kernelScalarUnitCharacter_value (T : Over S) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    (kernelScalarUnitCharacter D T z : Γ(T.left, ⊤)) = z.left.appTop D.kernelScalar :=
  congrArg z.left.appTop D.kernelScalar_isUnit.unit_spec

theorem kernelScalarUnitCharacter_recovers {T : Over S} (x : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    D.value x z = (kernelScalarUnitCharacter D T z : Γ(T.left, ⊤)) :=
  (Relative.KernelScalar.Construction.kernelScalar_value_of_projection_functions D x z).trans (kernelScalarUnitCharacter_value D T z).symm

theorem kernelScalarUnitCharacter_natural {T U : Over S} (t : U ⟶ T) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Units.map t.left.appTop.hom (kernelScalarUnitCharacter D T z) = kernelScalarUnitCharacter D U (t ≫ z) := by
  apply Units.ext
  change t.left.appTop (kernelScalarUnitCharacter D T z : Γ(T.left, ⊤)) =
    (kernelScalarUnitCharacter D U (t ≫ z) : Γ(U.left, ⊤))
  rw [kernelScalarUnitCharacter_value, kernelScalarUnitCharacter_value]
  exact (congrArg (fun m => m D.kernelScalar) (Scheme.Hom.comp_appTop t.left z.left)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.ScalarUnitCharacter.Construction
