import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteModuleSandwich
import Mathlib.Algebra.Module.Torsion.Free

/-! # Finite Torsion Free Sandwich -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTorsionFreeSandwich.Dimension

noncomputable section

/-! Clearing denominators gives generic-rank injections for finite torsion-free modules. -/

open scoped TensorProduct

theorem torsionFree_fractionTensor_injective
    (R K M : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Function.Injective (TensorProduct.mk R K M 1) := by
  let f : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
  have : IsLocalizedModule (nonZeroDivisors R) f := inferInstance
  apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors R) f).mpr
  intro s
  exact (IsRegular.of_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp s.property)).isSMulRegular

theorem finiteTorsionFreeModule_genericRank_injections
    (R K M : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    [Module.FinitePresentation R M] :
    ∃ (i : M →ₗ[R] (Fin (Module.finrank K
          (K ⊗[R] M)) →₀ R))
      (j : (Fin (Module.finrank K
          (K ⊗[R] M)) →₀ R) →ₗ[R] M),
      Function.Injective i ∧ Function.Injective j := by
  let V := K ⊗[R] M
  let d := Module.finrank K V
  let f : M →ₗ[R] V := TensorProduct.mk R K M 1
  let g : (Fin d →₀ R) →ₗ[R] (Fin d →₀ K) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap R K)
  have : IsLocalizedModule (nonZeroDivisors R) f := inferInstance
  have : IsLocalizedModule (nonZeroDivisors R) g := inferInstance
  have hf : Function.Injective f := torsionFree_fractionTensor_injective R K M
  have hg : Function.Injective g := by
    intro a b hab
    ext k
    apply IsFractionRing.injective R K
    exact DFunLike.congr_fun hab k
  let e : V ≃ₗ[R] (Fin d →₀ K) := (Module.finBasis K V).repr.restrictScalars R
  exact ArithmeticGeometry.OrdinaryLocus.Openness.FiniteModuleSandwich.Construction.exists_injective_maps_of_localized_equiv (nonZeroDivisors R) f g hf hg e

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTorsionFreeSandwich.Dimension
