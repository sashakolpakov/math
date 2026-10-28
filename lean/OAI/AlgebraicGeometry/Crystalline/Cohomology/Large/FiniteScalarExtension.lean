import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteFreeTensor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FlatScalarExtension
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Finite Scalar Extension -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteScalarExtension.LargeFiniteScalarExtension

noncomputable section

/-!
# Finite free scalar extension preserves the original large limits

The scalar action is the specified algebra action. Restricting it to
the base identifies scalar extension with the proved finite tensor
functor, and restriction of scalars reflects limits.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u v w

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def carrierIso (M : ModuleCat.{u + 2} R) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj ((FlatScalarExtension.LargeFlatScalarExtension.functor R S).obj M) ≅
      ModuleCat.of R (S ⊗[R] M) where
  hom := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((FlatScalarExtension.LargeFlatScalarExtension.functor R S).obj M))
    (Y := ModuleCat.of R (S ⊗[R] M))
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' r x := by
        exact algebraMap_smul (R := R) (M := S ⊗[R] M) S r x }
  inv := ModuleCat.ofHom
    (X := ModuleCat.of R (S ⊗[R] M))
    (Y := (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((FlatScalarExtension.LargeFlatScalarExtension.functor R S).obj M))
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' r x := by
        exact (algebraMap_smul (R := R) (M := S ⊗[R] M) S r x).symm }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

def restrictedIso :
    FlatScalarExtension.LargeFlatScalarExtension.functor R S ⋙ ModuleCat.restrictScalars (algebraMap R S) ≅
      FiniteFreeTensor.LargeFiniteFreeTensor.tensor R S :=
  NatIso.ofComponents (fun M => carrierIso R S M ≪≫ (TensorProduct.comm R S M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    ext x
    change TensorProduct.comm R S N ((f.hom.baseChange S) x) =
      TensorProduct.map f.hom LinearMap.id (TensorProduct.comm R S M x)
    induction x using TensorProduct.inductionOn with
    | tmul s m => rfl
    | add x y hx hy => simp only [map_add, hx, hy])

variable (ξ : Type u) [Fintype ξ] (b : Module.Basis ξ R S)

include b in
theorem preservesLimits [UnivLE.{v, u + 2}] :
    PreservesLimitsOfSize.{w, v} (FlatScalarExtension.LargeFlatScalarExtension.functor R S) := by
  have : PreservesLimitsOfSize.{w, v} (FiniteFreeTensor.LargeFiniteFreeTensor.tensor R S) :=
    FiniteFreeTensor.LargeFiniteFreeTensor.tensor_preservesLimits R S ξ b
  have : PreservesLimitsOfSize.{w, v}
      (FlatScalarExtension.LargeFlatScalarExtension.functor R S ⋙ ModuleCat.restrictScalars (algebraMap R S)) :=
    preservesLimits_of_natIso (restrictedIso R S).symm
  have : ReflectsLimitsOfSize.{w, v}
      (ModuleCat.restrictScalars.{u + 2} (algebraMap R S)) :=
    { reflectsLimitsOfShape := fun {J} _ =>
        { reflectsLimit := fun {F} =>
            { reflects := fun {c} hc => ⟨by
                have hc' := isLimitOfPreserves (forget₂ (ModuleCat.{u + 2} R) AddCommGrpCat) hc
                exact isLimitOfReflects (forget₂ (ModuleCat.{u + 2} S) AddCommGrpCat) hc'⟩ } } }
  exact preservesLimits_of_reflects_of_preserves (FlatScalarExtension.LargeFlatScalarExtension.functor R S)
    (ModuleCat.restrictScalars (algebraMap R S))

instance finiteFree_preservesLimits [Module.Free R S] [Module.Finite R S] [UnivLE.{v, u + 2}] :
    PreservesLimitsOfSize.{w, v} (FlatScalarExtension.LargeFlatScalarExtension.functor R S) :=
  preservesLimits R S (Module.Free.ChooseBasisIndex R S) (Module.Free.chooseBasis R S)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteScalarExtension.LargeFiniteScalarExtension
