import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.FinitePresentation

/-! # Finite Module Sandwich -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteModuleSandwich.Construction

noncomputable section

/-! A finite flat module over a domain admits injections to and from a free module
of its generic rank. The maps come from clearing denominators in a generic basis. -/

open scoped TensorProduct

theorem exists_injective_maps_of_localized_equiv
    {R M N M' N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (S : Submonoid R) (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g]
    (hf : Function.Injective f) (hg : Function.Injective g) (e : M' ≃ₗ[R] N') :
    ∃ (i : M →ₗ[R] N) (j : N →ₗ[R] M),
      Function.Injective i ∧ Function.Injective j := by
  obtain ⟨i, s, hi⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S g (e.toLinearMap.comp f)
  obtain ⟨j, t, hj⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S f (e.symm.toLinearMap.comp g)
  refine ⟨i, j, ?_, ?_⟩
  · intro x y hxy
    apply hf
    apply e.injective
    apply IsLocalizedModule.smul_injective g s
    have hx := LinearMap.congr_fun hi x
    have hy := LinearMap.congr_fun hi y
    exact hx.symm.trans ((congrArg g hxy).trans hy)
  · intro x y hxy
    apply hg
    apply e.symm.injective
    apply IsLocalizedModule.smul_injective f t
    have hx := LinearMap.congr_fun hj x
    have hy := LinearMap.congr_fun hj y
    exact hx.symm.trans ((congrArg f hxy).trans hy)

theorem finiteFlatModule_genericRank_injections
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module.FinitePresentation R M] :
    ∃ (i : M →ₗ[R] (Fin (Module.finrank (FractionRing R)
          (FractionRing R ⊗[R] M)) →₀ R))
      (j : (Fin (Module.finrank (FractionRing R)
          (FractionRing R ⊗[R] M)) →₀ R) →ₗ[R] M),
      Function.Injective i ∧ Function.Injective j := by
  let K := FractionRing R
  let V := K ⊗[R] M
  let d := Module.finrank K V
  let f : M →ₗ[R] V := TensorProduct.mk R K M 1
  let g : (Fin d →₀ R) →ₗ[R] (Fin d →₀ K) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap R K)
  have : IsLocalizedModule (nonZeroDivisors R) f := by
    dsimp [f, V, K]
    infer_instance
  have : IsLocalizedModule (nonZeroDivisors R) g := by
    dsimp [g, K]
    infer_instance
  have hf : Function.Injective f := Module.Flat.tensorProduct_mk_injective R M K
  have hg : Function.Injective g := by
    intro a b hab
    ext k
    apply IsFractionRing.injective R K
    exact DFunLike.congr_fun hab k
  let e : V ≃ₗ[R] (Fin d →₀ K) := (Module.finBasis K V).repr.restrictScalars R
  exact exists_injective_maps_of_localized_equiv (nonZeroDivisors R) f g hf hg e

theorem finiteFlatModule_genericRank_eq_rankAtStalk
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] [Module.Finite R M] :
    Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) =
      Module.rankAtStalk (R := R) M (⊥ : PrimeSpectrum R) := by
  let K := FractionRing R
  let q : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  have hq : q.comap (algebraMap R K) = ⊥ := by
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot (algebraMap R K)).mp
      (IsFractionRing.injective R K)
  have h := Module.rankAtStalk_baseChange (R := R) (M := M) q
  rw [Module.rankAtStalk_eq_finrank_of_free, hq] at h
  exact h

theorem finiteFlatModule_rankAtStalk_injections
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module.FinitePresentation R M] :
    ∃ (i : M →ₗ[R] (Fin (Module.rankAtStalk (R := R) M (⊥ : PrimeSpectrum R)) →₀ R))
      (j : (Fin (Module.rankAtStalk (R := R) M (⊥ : PrimeSpectrum R)) →₀ R) →ₗ[R] M),
      Function.Injective i ∧ Function.Injective j := by
  rw [← finiteFlatModule_genericRank_eq_rankAtStalk R M]
  exact finiteFlatModule_genericRank_injections R M

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteModuleSandwich.Construction
