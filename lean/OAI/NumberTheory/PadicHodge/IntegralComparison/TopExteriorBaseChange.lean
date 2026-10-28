import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Top Exterior Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorBaseChange

noncomputable section

/-! Top exterior powers of finite free modules commute with arbitrary
scalar extension, including quotient rings. The map is the canonical
exterior scalar-extension map and is independent of the chosen basis. -/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {V : Type*} [AddCommGroup V] [Module R V] {n : ℕ}
  (b : Module.Basis (Fin n) R V)

def topBasis : Module.Basis Unit R (⋀[R]^n V) :=
  (Module.Basis.singleton Unit R).map (TopExteriorCoordinates.equiv b).symm

theorem topBasis_apply (i : Unit) : topBasis b i = exteriorPower.ιMulti R n b := by
  simp [topBasis, TopExteriorCoordinates.generator]

def equiv : S ⊗[R] (⋀[R]^n V) ≃ₗ[S] ⋀[S]^n (S ⊗[R] V) :=
  ((topBasis b).baseChange S).equiv (topBasis (b.baseChange S)) (Equiv.refl Unit)

theorem equiv_eq : (TopExteriorBaseChange.equiv S b).toLinearMap = GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap R S V n := by
  apply ((topBasis b).baseChange S).ext
  intro i
  change ((topBasis b).baseChange S).equiv (topBasis (b.baseChange S)) (Equiv.refl Unit)
    ((topBasis b).baseChange S i) = _
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.baseChange_apply,
    topBasis_apply, topBasis_apply, GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap_tmul_ιMulti, one_smul]
  congr 1
  funext j
  exact Module.Basis.baseChange_apply S b j

theorem equiv_tmul_ιMulti (a : S) (v : Fin n → V) :
    TopExteriorBaseChange.equiv S b (a ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      a • exteriorPower.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) := by
  change (TopExteriorBaseChange.equiv S b).toLinearMap _ = _
  rw [equiv_eq, GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap_tmul_ιMulti]

theorem independent_basis (b' : Module.Basis (Fin n) R V) : TopExteriorBaseChange.equiv S b = TopExteriorBaseChange.equiv S b' := by
  apply LinearEquiv.toLinearMap_injective
  rw [equiv_eq, equiv_eq]

theorem composite_tmul {M : Type*} [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] ⋀[R]^n V) (a : S) (m : M) :
    ((e.baseChange R S M (⋀[R]^n V)).trans (TopExteriorBaseChange.equiv S b)) (a ⊗ₜ[R] m) =
      GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap R S V n (a ⊗ₜ[R] e m) := by
  change (TopExteriorBaseChange.equiv S b).toLinearMap (a ⊗ₜ[R] e m) = _
  rw [equiv_eq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorBaseChange
