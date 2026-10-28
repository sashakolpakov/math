import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OneSidedTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.TorRestriction

/-! # Derived Scalar Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedScalarExtension

noncomputable section

/-! Derived scalar extension retains the coefficient-ring action.
Flat extension of that coefficient ring commutes with these modules. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

variable (R T U : Type) [CommRing R] [CommRing T] [CommRing U]
  [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]

def assocIso : 𝟭 (ModuleCat R) ⋙ ProjectionFormula.Flat.Extension.baseChange R U ≅ ProjectionFormula.Flat.Extension.baseChange R T ⋙ ProjectionFormula.Flat.Extension.baseChange T U :=
  NatIso.ofComponents (fun M =>
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R T U U M).symm.toModuleIso) (by
      intro M M' f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul u m => rfl
      | add x y hx hy => simp only [map_add, hx, hy])

def derivedIso [Module.Flat T U] (M : ModuleCat R) (i : ℕ) :
    ((ProjectionFormula.Flat.Extension.baseChange R U).leftDerived i).obj M ≅
      (ProjectionFormula.Flat.Extension.baseChange T U).obj (((ProjectionFormula.Flat.Extension.baseChange R T).leftDerived i).obj M) :=
  DerivedBaseChange.leftDerivedIso (ProjectionFormula.Flat.Extension.baseChange R T) (ProjectionFormula.Flat.Extension.baseChange R U) (𝟭 _) (ProjectionFormula.Flat.Extension.baseChange T U)
    (assocIso R T U) M i

def restrictIso : 𝟭 (ModuleCat R) ⋙ MixedTensor.tensor R T (.of T U) ≅
    ProjectionFormula.Flat.Extension.baseChange R U ⋙ ModuleCat.restrictScalars (algebraMap T U) :=
  NatIso.ofComponents (fun M =>
    (show U ⊗[R] M ≃ₗ[T] (ModuleCat.restrictScalars (algebraMap T U)).obj ((ProjectionFormula.Flat.Extension.baseChange R U).obj M) from
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun t x => (algebraMap_smul U t (show U ⊗[R] M from x)).symm }).toModuleIso) (by
    intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul u m => rfl
    | add x y hx hy => simp only [map_add, hx, hy])

def restrictedDerivedIso (M : ModuleCat R) (i : ℕ) :
    ((MixedTensor.tensor R T (.of T U)).leftDerived i).obj M ≅
      (ModuleCat.restrictScalars (algebraMap T U)).obj (((ProjectionFormula.Flat.Extension.baseChange R U).leftDerived i).obj M) :=
  DerivedBaseChange.leftDerivedIso (ProjectionFormula.Flat.Extension.baseChange R U) (MixedTensor.tensor R T (.of T U))
    (𝟭 _) (ModuleCat.restrictScalars (algebraMap T U)) (restrictIso R T U) M i

def torIso [Module.Flat R T] (M : ModuleCat R) (i : ℕ) :
    (((Tor (ModuleCat T) i).obj ((ProjectionFormula.Flat.Extension.baseChange R T).obj M)).obj (.of T U)) ≅
      (ModuleCat.restrictScalars (algebraMap T U)).obj (((ProjectionFormula.Flat.Extension.baseChange R U).leftDerived i).obj M) :=
  ProjectionFormula.Tor.Symmetry.iso T _ (.of T U) i ≪≫
    OneSidedTor.derivedIso R T M (.of T U) i ≪≫ restrictedDerivedIso R T U M i

theorem quotient_length [Module.Flat R T] (h : Function.Surjective (algebraMap T U))
    (M : ModuleCat R) (i : ℕ) :
    Module.length T (((Tor (ModuleCat T) i).obj ((ProjectionFormula.Flat.Extension.baseChange R T).obj M)).obj (.of T U)) =
      Module.length U (((ProjectionFormula.Flat.Extension.baseChange R U).leftDerived i).obj M) := by
  rw [(torIso R T U M i).toLinearEquiv.length_eq]
  let N := ((ProjectionFormula.Flat.Extension.baseChange R U).leftDerived i).obj M
  let L := (ModuleCat.restrictScalars (algebraMap T U)).obj N
  let : IsScalarTower T U L := IsScalarTower.of_compHom T U N
  exact Module.length_eq_of_surjective (M := L) h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedScalarExtension
