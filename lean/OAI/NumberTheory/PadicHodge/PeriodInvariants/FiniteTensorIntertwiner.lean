import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ContinuousOrbit

/-! # Finite Tensor Intertwiner -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorIntertwiner

noncomputable section

/-! # The continuous finite tensor matrix is equivariant on coefficient representations -/

open ContRepresentation OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates OAI.NumberTheory.PadicHodge.PeriodInvariants.ContinuousOrbit.PiRepresentation

variable {R G M N E F I J : Type*} [CommRing R] [TopologicalSpace R] [Monoid G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul R M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def matrixIntertwiner (b : Module.Basis I R E) (c : Module.Basis J R F)
    {ρ : ContRepresentation R G M} {σ : ContRepresentation R G N}
    (f : ρ →ⁱL σ) (g : E →ₗ[R] F) : ContinuousOrbit.PiRepresentation.piRepresentation (I := I) ρ →ⁱL ContinuousOrbit.PiRepresentation.piRepresentation (I := J) σ where
  toContinuousLinearMap := FiniteTensorCoordinates.matrixMap b c f.toContinuousLinearMap g
  isIntertwining' a := by
    apply ContinuousLinearMap.ext
    intro v
    funext j
    change FiniteTensorCoordinates.matrixMap b c f.toContinuousLinearMap g (fun i => ρ a (v i)) j =
      σ a (FiniteTensorCoordinates.matrixMap b c f.toContinuousLinearMap g v j)
    rw [FiniteTensorCoordinates.matrixMap_apply, FiniteTensorCoordinates.matrixMap_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    exact congrArg (fun x => c.repr (g (b i)) j • x) (f.isIntertwining a (v i))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorIntertwiner
