import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BaseChangeRightExact

/-! # Tensor Cancel -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorCancel

noncomputable section

/-! The actual tensor cancellation for an S-module and an R-module,
as a natural isomorphism on the underlying R-module functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

local instance (M : ModuleCat.{u} S) :
    IsScalarTower R S ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def cancel (M : ModuleCat.{u} S) (N : ModuleCat.{u} R) :
    M ⊗[S] (S ⊗[R] N) ≃ₗ[S]
      ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ⊗[R] N :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R S S
    ((ModuleCat.restrictScalars (algebraMap R S)).obj M) N

theorem cancel_algebraMap_smul (M : ModuleCat.{u} S) (N : ModuleCat.{u} R) (r : R)
    (t : M ⊗[S] (S ⊗[R] N)) :
    cancel R S M N ((algebraMap R S r) • t) = r • cancel R S M N t := by
  rw [map_smul]
  exact IsScalarTower.algebraMap_smul S r (cancel R S M N t)

def component (M : ModuleCat.{u} S) (N : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj ((tensorLeft M).obj ((FlatExtension.baseChange R S).obj N)) ≃ₗ[R]
      (tensorLeft ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).obj N where
  __ := (cancel R S M N).toAddEquiv
  map_smul' r t := cancel_algebraMap_smul R S M N r t

def tensorCancelIso (M : ModuleCat.{u} S) :
    (FlatExtension.baseChange R S ⋙ tensorLeft M) ⋙ ModuleCat.restrictScalars (algebraMap R S) ≅
      tensorLeft ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
  NatIso.ofComponents (fun N => (component R S M N).toModuleIso) (by
    intro N N' f
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul m t =>
      induction t using TensorProduct.inductionOn with
      | tmul s n => rfl
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb])

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorCancel
