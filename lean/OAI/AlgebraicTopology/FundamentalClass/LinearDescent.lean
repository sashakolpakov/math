import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Linear Descent -/

namespace OAI.AlgebraicTopology.FundamentalClass.LinearDescent.IntegrationConstruction

noncomputable section

/-! Integration: elementary descent of actual chain functionals to quotient chains
and homology. These lemmas contain no geometric comparison assumption. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

variable {F : Type} [Field F]

def factorFunctional {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (π : V →ₗ[F] W) (hπ : Function.Surjective π)
    (L : V →ₗ[F] F) (hL : LinearMap.ker π ≤ LinearMap.ker L) : W →ₗ[F] F :=
  ((LinearMap.ker π).liftQ L hL).comp (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

theorem factorFunctional_apply {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (π : V →ₗ[F] W) (hπ : Function.Surjective π)
    (L : V →ₗ[F] F) (hL : LinearMap.ker π ≤ LinearMap.ker L) (v : V) :
    factorFunctional π hπ L hL (π v) = L v := by
  simp only [factorFunctional, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

def chainFunctionalOnHomology (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (L : C.X n →ₗ[F] F) (hL : ∀ (i : ℕ) (v : C.X i), L (C.d i n v) = 0) :
    C.homology n →ₗ[F] F :=
  ((Cohomology.Singular.ChainRepresentatives.chainBoundaries C n).liftQ (L.comp (Cohomology.Singular.ChainRepresentatives.chainCycles C n).subtype)
    (by
      rintro z ⟨v, rfl⟩
      exact hL _ v)).comp (Cohomology.Singular.ChainRepresentatives.homologyQuotientIso C n).toLinearEquiv.toLinearMap

theorem chainFunctionalOnHomology_class (C : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (L : C.X n →ₗ[F] F) (hL : ∀ (i : ℕ) (v : C.X i), L (C.d i n v) = 0)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    chainFunctionalOnHomology C n L hL (Cohomology.Singular.ChainRepresentatives.chainClass C n z) = L z.val := by
  dsimp only [chainFunctionalOnHomology, Cohomology.Singular.ChainRepresentatives.chainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicTopology.FundamentalClass.LinearDescent.IntegrationConstruction
