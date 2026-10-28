import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalSourceCotangentAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DoubleAltBasis

/-! # Source Tensor Cotangent Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceTensorCotangentProjection.CM

noncomputable section

/-! Double alternation of the full adapted tensor gives the literal
source theta coefficient, and cotangent changes act by their actual
two-dimensional determinant. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

theorem double_alt_tangent_bilinear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Q : V →L[ℂ] V →L[ℂ] ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (u : Fin 2 × Fin 2 → V) :
    RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => Q (∑ k : Fin 2, B a.1 k • u (k, a.2))
      (∑ k : Fin 2, B b.1 k • u (k, b.2))) =
      B.det * RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => Q (u a) (u b)) := by
  simp only [RepresentationTheory.Theta.Kernel.Calculus.doubleAlt, Fin.sum_univ_two, map_add, map_smul, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, Matrix.det_fin_two]
  ring

theorem double_alt_tangent_tensor {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : V [×2]→L[ℂ] ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (u : Fin 2 × Fin 2 → V) :
    RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => H ![∑ k : Fin 2, B a.1 k • u (k, a.2),
      ∑ k : Fin 2, B b.1 k • u (k, b.2)]) = B.det * RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => H ![u a, u b]) := by
  let Q : V →L[ℂ] V →L[ℂ] ℂ :=
    (continuousMultilinearCurryFin1 ℂ V ℂ : (V [×1]→L[ℂ] ℂ) →L[ℂ] V →L[ℂ] ℂ).comp H.curryLeft
  have hQ (x y : V) : Q x y = H ![x, y] := by
    change continuousMultilinearCurryFin1 ℂ V ℂ (H.curryLeft x) y = _
    simp only [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  simpa only [hQ] using double_alt_tangent_bilinear Q B u

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Gal(K/ℚ) → Bool}
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places))

theorem source_adapted_tensor_slots (z : HeckeCycles.GeometricSource.CM.BallChart) (a b : Fin 2 × Fin 2) :
    ConcreteApproximationFrameAction.CM.sourceAdaptedThetaTensor K L φ 2 z
      ![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b] =
      InitialTensor.CM.splitThetaTensor K (L 0) (L 1) φ z a b := by
  change (((L 0).halfDet z : ℂ) * ((L 1).halfDet z : ℂ)) *
    iteratedFDeriv ℂ 2 (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z))) 0
      (fun j => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z)ᵀ.mulVec
        (![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b] j)) = _
  have hu : (fun j : Fin 2 => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z)ᵀ.mulVec
      (![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b] j)) =
      ![InitialTensor.CM.splitThetaSlot K (L 0) (L 1) z a, InitialTensor.CM.splitThetaSlot K (L 0) (L 1) z b] := by
    funext j
    fin_cases j
    · exact (TotalAdaptedDualSlots.CM.split_theta_slot_adapted_transpose K L z a).symm
    · exact (TotalAdaptedDualSlots.CM.split_theta_slot_adapted_transpose K L z b).symm
  rw [hu]
  rfl

omit L φ in
theorem total_adapted_tangent_basis (places : HeckeCycles.GeometricSource.CM.Places K) (i j : Fin 2) :
    TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K places j ((Pi.basisFun ℂ (Fin 2)) i) = TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places (i, j) := by
  fin_cases i <;> simp [TotalSourceCotangentAction.CM.totalAdaptedTangentSlot, Pi.basisFun_apply]

theorem source_tangent_double_alt (z : HeckeCycles.GeometricSource.CM.BallChart) (T : HeckeCycles.GeometricSource.CM.BallChart →L[ℂ] HeckeCycles.GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => ConcreteApproximationFrameAction.CM.sourceAdaptedThetaTensor K L φ 2 z
      ![TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K places a.2 (T ((Pi.basisFun ℂ (Fin 2)) a.1)),
        TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K places b.2 (T ((Pi.basisFun ℂ (Fin 2)) b.1))]) =
      LinearMap.det T.toLinearMap * InitialTensor.CM.splitThetaTopCoefficient K (L 0) (L 1) φ z := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := fun i j => T ((Pi.basisFun ℂ (Fin 2)) i) j
  have hM : M = (LinearMap.toMatrix' T.toLinearMap)ᵀ := by
    apply Matrix.ext
    intro i j
    change T ((Pi.basisFun ℂ (Fin 2)) i) j = T (Pi.single i 1) j
    apply congrArg (fun u : HeckeCycles.GeometricSource.CM.BallChart => T u j)
    funext k
    simp [Pi.basisFun_apply, Pi.single_apply]
  have hd : M.det = LinearMap.det T.toLinearMap := by
    rw [hM, Matrix.det_transpose, LinearMap.det_toMatrix']
  have h := double_alt_tangent_tensor (ConcreteApproximationFrameAction.CM.sourceAdaptedThetaTensor K L φ 2 z) M
    (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places)
  rw [hd] at h
  simpa only [TotalSourceCotangentAction.CM.totalAdaptedTangentSlot, source_adapted_tensor_slots, InitialTensor.CM.splitThetaTopCoefficient] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceTensorCotangentProjection.CM
