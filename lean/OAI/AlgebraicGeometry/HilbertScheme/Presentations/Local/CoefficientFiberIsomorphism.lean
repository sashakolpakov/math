import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarTowerFiberIsomorphism
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Coefficient Fiber Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.CoefficientFiberIsomorphism

noncomputable section

/-! A map between finite modules over a noetherian local algebra is an
isomorphism if its coefficient closed fiber is and its target is coefficient-flat. -/

open TensorProduct

universe u v w t
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {B : Type v} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
variable [Algebra R B] [IsLocalHom (algebraMap R B)]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

theorem localAlgebraModule_bijective_of_closedFiber
    (f : M →ₗ[B] N) [Module.Finite B M] [Module.Finite B N] [Module.Flat R N]
    (h : Function.Bijective ((f.restrictScalars R).lTensor (IsLocalRing.ResidueField R))) :
    Function.Bijective f := by
  apply ScalarTowerFiberIsomorphism.scalarTower_bijective_of_quotientTensor_of_flat (IsLocalRing.maximalIdeal R) _ f h
  apply le_trans _ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]

theorem localAlgebra_bijective_of_closedFiber
    {C : Type w} [CommRing C] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Module.Finite B C] [Module.Flat R C]
    (h : Function.Bijective (((Algebra.linearMap B C).restrictScalars R).lTensor
      (IsLocalRing.ResidueField R))) : Function.Bijective (algebraMap B C) :=
  localAlgebraModule_bijective_of_closedFiber (Algebra.linearMap B C) h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.CoefficientFiberIsomorphism
