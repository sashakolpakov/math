import OAI.RepresentationTheory.Theta.Adelic.GeometricFrameSmoothness
import OAI.RepresentationTheory.Theta.Adelic.TensorSmoothness
import OAI.RepresentationTheory.Theta.Adelic.Regularity

/-! # Geometric Tensor Smoothness -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricTensorSmoothness

noncomputable section

/-! Smooth completed theta tensors in the actual Hodge frame and
independently constructed half-determinant line. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.GeometricFrameSmoothness OAI.RepresentationTheory.Theta.Adelic.TensorSmoothness OAI.RepresentationTheory.Theta.Adelic.Regularity OAI.RepresentationTheory.Theta.Adelic.Prerequisites

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem geometricTensor_smooth (h : Prerequisites.ThetaInput.{0}) (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ) :
    BallGeometryData.BallSmooth (DataTheta.geometricTensor (GeometricGaussians.constructedComparison A P) f a) := by
  let Z : (Fin 2 → ℂ) → Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
    fun z => if hz : z ∈ BallGeometryData.ballDomain then (PeriodCoordinates.geometricPeriod A P ⟨z, hz⟩).matrix else 0
  let Q : (Fin 2 → ℂ) → Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
    fun z => if hz : z ∈ BallGeometryData.ballDomain then (PeriodCoordinates.geometricPositionUnit A P ⟨z, hz⟩).inv else 0
  let c : (Fin 2 → ℂ) → ℂ :=
    fun z => if hz : z ∈ BallGeometryData.ballDomain then GeometricHalfFrame.geometricHalfFrame A P ⟨z, hz⟩ else 0
  have hZ : ContDiffOn ℝ ⊤ Z BallGeometryData.ballDomain := GeometricFrameSmoothness.period_matrix_smooth A P
  have hQ : ContDiffOn ℝ ⊤ Q BallGeometryData.ballDomain := GeometricFrameSmoothness.position_inverse_smooth A P
  have hc : ContDiffOn ℝ ⊤ c BallGeometryData.ballDomain := GeometricFrameSmoothness.half_frame_smooth A P
  have hm : Set.MapsTo Z BallGeometryData.ballDomain Definitions.siegelDomain := by
    intro z hz
    change (Z z).IsSymm ∧ Matrix.PosDef (fun i j => (Z z i j).im)
    simp only [Z, dite_eq_left hz]
    exact ⟨(PeriodCoordinates.geometricPeriod A P ⟨z, hz⟩).symmetric,
      (PeriodCoordinates.geometricPeriod A P ⟨z, hz⟩).imaginary_posDef⟩
  have hT := (Regularity.completedTensor_smooth A P h f a).comp hZ hm
  have hM := TensorSmoothness.matrixOperator_contDiff.comp_contDiffOn
    (TensorSmoothness.matrix_transpose_contDiff.comp_contDiffOn hQ)
  have ht := TensorSmoothness.tensor_frame_smooth a
    (fun z => DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a (Z z))
    (fun z => (Matrix.toLin' (Q z)ᵀ).toContinuousLinearMap) hT hM
  have hn : ∀ z ∈ BallGeometryData.ballDomain, c z ≠ 0 := by
    intro z hz
    simp only [c, dite_eq_left hz]
    exact GeometricHalfFrame.geometricHalfFrame_nonzero A P ⟨z, hz⟩
  have hs : ContDiffOn ℝ ⊤ (fun z => (c z)⁻¹ •
      (DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a (Z z)).compContinuousLinearMap
        (fun _ => (Matrix.toLin' (Q z)ᵀ).toContinuousLinearMap)) BallGeometryData.ballDomain :=
    (hc.inv hn).smul ht
  apply hs.congr
  intro z hz
  simp only [Z, Q, c, dite_eq_left hz]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricTensorSmoothness
