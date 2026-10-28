import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear
import Mathlib.LinearAlgebra.Pi

/-! # Adic Finite Modules -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicFiniteModules

noncomputable section

/-! # Adic completeness transfers through linear equivalences and finite products -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (I : Ideal R)

theorem of_equiv [IsAdicComplete I M] (e : M ≃ₗ[R] N) : IsAdicComplete I N := by
  let t : N ≃ₗ[R] AdicCompletion I N :=
    e.symm.trans ((AdicCompletion.ofLinearEquiv I M).trans ((AdicCompletion.congr I e).restrictScalars R))
  have ht : (t : N → AdicCompletion I N) = AdicCompletion.of I N := by
    funext x
    change AdicCompletion.map I e (AdicCompletion.of I M (e.symm x)) = AdicCompletion.of I N x
    rw [AdicCompletion.map_of]
    exact congrArg (AdicCompletion.of I N) (e.apply_symm_apply x)
  apply AdicCompletion.of_bijective_iff.mp
  rw [← ht]
  exact t.bijective

theorem pi_complete {J : Type*} [Fintype J] [DecidableEq J] [IsAdicComplete I M] :
    IsAdicComplete I (J → M) := by
  let e := (AdicCompletion.piEquivOfFintype I (fun _ : J => M)).restrictScalars R
  let t : (J → M) ≃ₗ[R] AdicCompletion I (J → M) :=
    (LinearEquiv.piCongrRight (fun _ : J => AdicCompletion.ofLinearEquiv I M)).trans e.symm
  have ht : (t : (J → M) → AdicCompletion I (J → M)) = AdicCompletion.of I (J → M) := by
    funext x
    apply e.injective
    change e (e.symm (fun j => AdicCompletion.of I M (x j))) = e (AdicCompletion.of I (J → M) x)
    rw [LinearEquiv.apply_symm_apply]
    funext j
    change AdicCompletion.of I M (x j) =
      AdicCompletion.piEquivOfFintype I (fun _ : J => M) (AdicCompletion.of I (J → M) x) j
    rw [AdicCompletion.piEquivOfFintype_apply]
    exact (AdicCompletion.map_of I (LinearMap.proj j) x).symm
  apply AdicCompletion.of_bijective_iff.mp
  rw [← ht]
  exact t.bijective

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicFiniteModules
