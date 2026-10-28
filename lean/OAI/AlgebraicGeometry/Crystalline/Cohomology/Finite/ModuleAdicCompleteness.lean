import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Module Adic Completeness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness.FiniteModuleAdicCompleteness

noncomputable section

/-! # Finite modules over a complete noetherian ring are complete via the actual completion map -/

open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R]

theorem finite_small (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] : Small.{u} M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact small_of_surjective hf

variable [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

section SameUniverse

variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

def smallEquiv : M ≃ₗ[R] AdicCompletion I M :=
  (TensorProduct.lid R M).symm.trans
    ((TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M)).trans
      ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R))

theorem smallEquiv_apply (x : M) : smallEquiv R I M x = AdicCompletion.of I M x := by
  change AdicCompletion.ofTensorProduct I M ((AdicCompletion.of I R 1) ⊗ₜ[R] x) = _
  rw [AdicCompletion.ofTensorProduct_tmul]
  change (1 : AdicCompletion I R) • AdicCompletion.of I M x = _
  exact one_smul _ _

end SameUniverse

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

def equiv : M ≃ₗ[R] AdicCompletion I M := by
  let : Small.{u} M := finite_small R M
  let e : Shrink.{u} M ≃ₗ[R] M := Shrink.linearEquiv R M
  let eAll : M ≃ AdicCompletion I M :=
    e.symm.toEquiv.trans ((smallEquiv R I (Shrink.{u} M)).toEquiv.trans
      (AdicCompletion.congr I e).toEquiv)
  have he (x : M) : eAll x = AdicCompletion.of I M x := by
    change AdicCompletion.map I e.toLinearMap
      (smallEquiv R I (Shrink.{u} M) (e.symm x)) = _
    rw [smallEquiv_apply, AdicCompletion.map_of]
    exact congrArg (AdicCompletion.of I M) (e.apply_symm_apply x)
  apply LinearEquiv.ofBijective (AdicCompletion.of I M)
  rw [← show (eAll : M → AdicCompletion I M) = AdicCompletion.of I M from funext he]
  exact eAll.bijective

theorem equiv_apply (x : M) : equiv R I M x = AdicCompletion.of I M x := rfl

theorem complete : IsAdicComplete I M := by
  apply AdicCompletion.of_bijective_iff.mp
  have h : (equiv R I M : M → AdicCompletion I M) = AdicCompletion.of I M :=
    funext (equiv_apply R I M)
  rw [← h]
  exact (equiv R I M).bijective

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness.FiniteModuleAdicCompleteness
