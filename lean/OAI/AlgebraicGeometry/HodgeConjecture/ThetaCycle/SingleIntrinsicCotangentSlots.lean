import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGeometricTensor
import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice

/-! # Single Intrinsic Cotangent Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleIntrinsicCotangentSlots.CM

noncomputable section

/-! The fixed source cotangent slots are exactly a single nonzero scalar
times the actual distinguished slots of the native ThetaOneForms one-form. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

section

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (j : Fin 2)

theorem direct_single_frame_coefficient_diagonal :
    SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j =
      Matrix.diagonal (fun p : HeckeCycles.GeometricSource.CM.Positions K places => SourceFrameComponents.CM.directSourceFrameScale K Q p.1 (p.2, j)) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  rw [SingleLineFrameDeterminant.CM.direct_single_indexed_frame_coefficient_apply]
  funext p
  rw [Matrix.mulVec_diagonal]
  rfl

def singleNativeCotangentScale : ℂ := SourceFrameComponents.CM.directSourceFrameScale K Q places.distinguished (1, j)

theorem single_native_cotangent_scale_ne_zero : singleNativeCotangentScale K Q j ≠ 0 :=
  SourceFrameComponents.CM.direct_source_frame_scale_ne_zero K Q places.distinguished (1, j)

theorem single_native_cotangent_scale_slot (i : Fin 2) :
    SourceFrameComponents.CM.directSourceFrameScale K Q places.distinguished (i.succ, j) = singleNativeCotangentScale K Q j := by
  fin_cases i <;> simp [singleNativeCotangentScale, SourceFrameComponents.CM.directSourceFrameScale]

end

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)

theorem direct_single_native_dual_apply (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ)
    (p : Fin places.count × (Fin 3 × Fin 1)) :
    SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j u p =
      (SourceFrameComponents.CM.directSourceFrameScale K Q p.1 (p.2.1, j))⁻¹ * u (p.1, p.2.1) := by
  have hi : (SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j)⁻¹ =
      Matrix.diagonal (fun p : HeckeCycles.GeometricSource.CM.Positions K places => (SourceFrameComponents.CM.directSourceFrameScale K Q p.1 (p.2, j))⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [direct_single_frame_coefficient_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (SourceFrameComponents.CM.direct_source_frame_scale_ne_zero K Q _ _), Matrix.diagonal_one]
  rw [SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates, hi, Matrix.diagonal_transpose, Matrix.mulVec_diagonal]
  rfl

theorem direct_single_native_dual_slot (i : Fin 2) :
    SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i) =
      (singleNativeCotangentScale K Q j)⁻¹ • Pi.single
        (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) i) 1 := by
  funext p
  rcases p with ⟨v, k, l⟩
  fin_cases l
  rw [direct_single_native_dual_apply]
  change (SourceFrameComponents.CM.directSourceFrameScale K Q v (k, j))⁻¹ *
    (Pi.single (places.distinguished, i.succ) 1 : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) (v, k) =
      (singleNativeCotangentScale K Q j)⁻¹ *
        (Pi.single (places.distinguished, i.succ, (0 : Fin 1)) 1 :
          Fin places.count × (Fin 3 × Fin 1) → ℂ) (v, k, 0)
  by_cases h : places.distinguished = v ∧ i.succ = k
  · rcases h with ⟨rfl, rfl⟩
    simp only [Pi.single_eq_same, mul_one, single_native_cotangent_scale_slot]
  · have hn : ¬ (v = places.distinguished ∧ k = i.succ) :=
      fun hh => h ⟨hh.1.symm, hh.2.symm⟩
    simp only [Pi.single_apply, Prod.mk.injEq, and_true, ite_eq_right hn, mul_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleIntrinsicCotangentSlots.CM
