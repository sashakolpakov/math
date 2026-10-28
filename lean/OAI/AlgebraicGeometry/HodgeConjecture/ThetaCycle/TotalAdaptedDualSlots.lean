import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalGraphSlots

/-! # Total Adapted Dual Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalAdaptedDualSlots.CM

noncomputable section

/-! The literal source theta slots are duals of the fixed distinguished
adapted coordinates. Their dependence on the period is exactly the
transpose of the actual adapted graph matrix. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def totalAdaptedDualSlot (places : HeckeCycles.GeometricSource.CM.Places K) (a : Fin 2 × Fin 2) : PeriodTotal.CM.TotalPositions K places → ℂ :=
  Pi.single (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished a.1.succ a.2) 1

theorem total_adapted_distinguished_coordinate (d : Fin 2 → Gal(K/ℚ) → Bool)
    (w : ComplexTransition.CM.TotalAmbient K) (a : Fin 2 × Fin 2) :
    AdaptedTotal.CM.totalAdaptedCoordinates K places d w (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished a.1.succ a.2) =
      w a.2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) a.1.castSucc := by
  rcases a with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [AdaptedTotal.CM.totalAdaptedCoordinates, SourceFrameComponents.CM.sourceTotalSlot, HeckeCycles.GeometricSource.CM.adaptedCoordinates, places.identity]

theorem split_theta_slot_adapted_transpose
    {d : Fin 2 → Gal(K/ℚ) → Bool} (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (a : Fin 2 × Fin 2) :
    InitialTensor.CM.splitThetaSlot K (L 0) (L 1) z a =
      (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z)ᵀ.mulVec (totalAdaptedDualSlot K places a) := by
  have hC : ![(L 0).coordinates, (L 1).coordinates] = fun j => (L j).coordinates := by
    funext j
    fin_cases j <;> rfl
  rw [← TotalGraphSlots.CM.total_graph_slot_block, hC]
  funext j
  rw [TotalGraphSlots.CM.total_graph_slot_apply]
  change _ = (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z)ᵀ.mulVec
    (Pi.single (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished a.1.succ a.2) 1) j
  rw [Matrix.mulVec_single_one]
  change _ = SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z
    (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished a.1.succ a.2) j
  rw [SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix, LinearMap.toMatrix'_apply]
  simpa only [Pi.basisFun_apply, Pi.single_apply, LinearMap.comp_apply] using!
    (total_adapted_distinguished_coordinate K (places := places) d
    (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
      (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) ((Pi.basisFun ℂ _) j)) a).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalAdaptedDualSlots.CM
