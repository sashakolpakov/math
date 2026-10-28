import OAI.NumberTheory.PadicHodge.PeriodInvariants.TensorCoordinateNaturality
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicFiniteModules
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Finite Tensor Completion -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCompletion

noncomputable section

/-! # Completion commutes with tensoring by a finite free module -/

open scoped TensorProduct

variable {R M E K : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup E] [Module R E] [Fintype K] [DecidableEq K]
  (I : Ideal R) (b : Module.Basis K R E)

def completedCoordinates : AdicCompletion I (M ⊗[R] E) ≃ₗ[R] (K → AdicCompletion I M) :=
  ((AdicCompletion.congr I (FiniteTensorCoordinates.coordinates b)).restrictScalars R).trans
    ((AdicCompletion.piEquivOfFintype I (fun _ : K => M)).restrictScalars R)

def equiv : AdicCompletion I (M ⊗[R] E) ≃ₗ[R] (AdicCompletion I M ⊗[R] E) :=
  (completedCoordinates I b).trans (FiniteTensorCoordinates.coordinates b).symm

theorem completedCoordinates_of (x : M ⊗[R] E) (k : K) :
    completedCoordinates I b (AdicCompletion.of I _ x) k =
      AdicCompletion.of I M (FiniteTensorCoordinates.coordinates b x k) := by
  change AdicCompletion.piEquivOfFintype I (fun _ : K => M)
    (AdicCompletion.map I (FiniteTensorCoordinates.coordinates b).toLinearMap (AdicCompletion.of I _ x)) k = _
  rw [AdicCompletion.map_of, AdicCompletion.piEquivOfFintype_apply]
  change AdicCompletion.map I (LinearMap.proj k : (K → M) →ₗ[R] M)
    (AdicCompletion.of I (K → M) (FiniteTensorCoordinates.coordinates b x)) = _
  exact AdicCompletion.map_of I (LinearMap.proj k : (K → M) →ₗ[R] M) _

theorem equiv_of (x : M ⊗[R] E) : equiv I b (AdicCompletion.of I _ x) =
    TensorProduct.map (AdicCompletion.of I M) (LinearMap.id : Module.End R E) x := by
  apply (FiniteTensorCoordinates.coordinates b).injective
  change FiniteTensorCoordinates.coordinates b
    ((FiniteTensorCoordinates.coordinates b).symm (completedCoordinates I b (AdicCompletion.of I _ x))) = _
  rw [LinearEquiv.apply_symm_apply]
  funext k
  exact (completedCoordinates_of I b x k).trans
    (TensorCoordinateNaturality.coordinate_map b (AdicCompletion.of I M) x k).symm

include b in
theorem tensor_complete (hI : I.FG) : IsAdicComplete I (AdicCompletion I M ⊗[R] E) := by
  have : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete hI
  have : IsAdicComplete I (K → AdicCompletion I M) := AdicFiniteModules.pi_complete I
  exact AdicFiniteModules.of_equiv I (FiniteTensorCoordinates.coordinates b).symm

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCompletion
