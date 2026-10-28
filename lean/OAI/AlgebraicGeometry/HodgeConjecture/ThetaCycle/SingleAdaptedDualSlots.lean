import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceHalfDetAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Slots

/-! # Single Adapted Dual Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleAdaptedDualSlots.CM

noncomputable section

/-! The one-line Jacobi slots are the transpose of the actual source
adapted graph applied to the fixed cotangent coordinates. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def singleAdaptedDualSlot (places : HeckeCycles.GeometricSource.CM.Places K) (i : Fin 2) : HeckeCycles.GeometricSource.CM.Positions K places → ℂ :=
  Pi.single (places.distinguished, i.succ) 1

theorem single_adapted_distinguished_coordinate (d : Gal(K/ℚ) → Bool) (w : HeckeCycles.GeometricSource.CM.Ambient K) (i : Fin 2) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d w (places.distinguished, i.succ) =
      w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) i.castSucc := by
  fin_cases i <;> simp [HeckeCycles.GeometricSource.CM.adaptedCoordinates, places.identity]

theorem theta_jacobi_slot_adapted_transpose {d : Gal(K/ℚ) → Bool}
    (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin 2) :
    Slots.CM.thetaJacobiSlot K L z i =
      (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z)ᵀ.mulVec (singleAdaptedDualSlot K places i) := by
  funext j
  change _ = (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z)ᵀ.mulVec (Pi.single (places.distinguished, i.succ) 1) j
  rw [Matrix.mulVec_single_one]
  change _ = SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z (places.distinguished, i.succ) j
  rw [SourceHalfDetAction.CM.sourceAdaptedGraphMatrix, LinearMap.toMatrix'_apply]
  simpa only [Slots.CM.thetaJacobiSlot, Slots.CM.graphCoefficient, Pi.basisFun_apply, Pi.single_apply, LinearMap.comp_apply] using!
    (single_adapted_distinguished_coordinate K (places := places) d
    (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) ((Pi.basisFun ℂ _) j)) i).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleAdaptedDualSlots.CM
