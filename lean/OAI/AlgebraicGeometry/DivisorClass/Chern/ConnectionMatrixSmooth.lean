import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionEnergyMatrix
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Connection Matrix Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionMatrixSmooth

noncomputable section

/-! Smoothness of each actual matrix block in a connection energy. -/

open scoped ContDiff

variable {F G D : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [CompleteSpace F] in
theorem connectionValueGradientMatrix_smoothOn (S : G →L[ℝ] G)
    (A : D → G →L[ℝ] G) (K : D → F →L[ℝ] G) {U : Set D}
    (hA : ContDiffOn ℝ ∞ A U) (hK : ContDiffOn ℝ ∞ K U) :
    ContDiffOn ℝ ∞ (fun x => ConnectionEnergyMatrix.connectionValueGradientMatrix (A x) S (K x)) U :=
  contDiffOn_const.clm_comp (hA.clm_comp hK)

theorem connectionGradientValueMatrix_smoothOn (S : G →L[ℝ] G)
    (A : D → G →L[ℝ] G) (K : D → F →L[ℝ] G) {U : Set D}
    (hA : ContDiffOn ℝ ∞ A U) (hK : ContDiffOn ℝ ∞ K U) :
    ContDiffOn ℝ ∞ (fun x => ConnectionEnergyMatrix.connectionGradientValueMatrix (A x) S (K x)) U := by
  have hAdj : ContDiff ℝ ∞ (ContinuousLinearMap.adjoint : (F →L[ℝ] G) → G →L[ℝ] F) :=
    (ContinuousLinearMap.adjoint : (F →L[ℝ] G) ≃ₗᵢ[ℝ] (G →L[ℝ] F)).toContinuousLinearEquiv.contDiff
  exact (hAdj.comp_contDiffOn hK).clm_comp (hA.clm_comp contDiffOn_const)

theorem connectionValueMatrix_smoothOn
    (A : D → G →L[ℝ] G) (K : D → F →L[ℝ] G) {U : Set D}
    (hA : ContDiffOn ℝ ∞ A U) (hK : ContDiffOn ℝ ∞ K U) :
    ContDiffOn ℝ ∞ (fun x => ConnectionEnergyMatrix.connectionValueMatrix (A x) (K x)) U := by
  have hAdj : ContDiff ℝ ∞ (ContinuousLinearMap.adjoint : (F →L[ℝ] G) → G →L[ℝ] F) :=
    (ContinuousLinearMap.adjoint : (F →L[ℝ] G) ≃ₗᵢ[ℝ] (G →L[ℝ] F)).toContinuousLinearEquiv.contDiff
  exact (hAdj.comp_contDiffOn hK).clm_comp (hA.clm_comp hK)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionMatrixSmooth
