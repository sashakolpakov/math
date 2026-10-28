import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Scalar Surjection Module Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ScalarSurjectionModuleRank.BundleCycles

noncomputable section

/-! The stalk rank of a finite flat module is unchanged by a surjective
scalar extension when the extended scalar action already exists. -/

open scoped TensorProduct

theorem moduleRankAtStalk_surjectiveScalars (R S M : Type) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R M] [Module.Flat R M] (h : Function.Surjective (algebraMap R S)) (p : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) M p = Module.rankAtStalk (R := R) M (p.comap (algebraMap R S)) := by
  let : TensorProduct.CompatibleSMul R S S M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S M h
  have hb : IsBaseChange S (LinearMap.id : M →ₗ[R] M) :=
    IsBaseChange.of_equiv (TensorProduct.lidOfCompatibleSMul R S M) (fun m => by
      rw [TensorProduct.lidOfCompatibleSMul_tmul, one_smul]
      rfl)
  exact Module.rankAtStalk_isBaseChange hb p

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ScalarSurjectionModuleRank.BundleCycles
