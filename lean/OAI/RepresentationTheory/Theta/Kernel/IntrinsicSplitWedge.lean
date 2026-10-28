import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis
import OAI.RepresentationTheory.Theta.Kernel.Calculus

/-! # Intrinsic Split Wedge -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitWedge.Intrinsic

noncomputable section

/-! The split native order-two projection equals the wedge of the two
actual ThetaOneForms one-forms, with the factorial normalization checked explicitly. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis.Intrinsic

theorem mixed_hessian_reverse {E E₁ E₂ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    (L : E →L[ℂ] E₁) (R : E →L[ℂ] E₂) (f : E₁ → ℂ) (g : E₂ → ℂ)
    (hf : ContDiff ℂ 2 f) (hg : ContDiff ℂ 2 g) (v w : E)
    (hv : L v = 0) (hw : R w = 0) :
    iteratedFDeriv ℂ 2 (fun y => f (L y) * g (R y)) 0 ![v,w] =
      fderiv ℂ f 0 (L w) * fderiv ℂ g 0 (R v) := by
  have he : (fun y => f (L y) * g (R y)) = (fun y => g (R y) * f (L y)) :=
    funext fun y => mul_comm _ _
  rw [he]
  exact (Calculus.mixed_hessian R L g f hg hf v w hw hv).trans (mul_comm _ _)

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))

def leftProjection : ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) → ℂ) →L[ℂ]
    (Adelic.BallGeometryData.FrameIndex A → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (.inl i)

def rightProjection : ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) → ℂ) →L[ℂ]
    (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (.inr i)

theorem thetaOneForm_apply_jacobi (f : Adelic.FiniteSchwartz.finiteSchwartz F 3) (z : Adelic.BallNatural.Ball) (u : IntrinsicExterior.Intrinsic.Tangent) :
    OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ f z u =
      (B₁.halfFrame z)⁻¹ *
        fderiv ℂ (Adelic.DataTheta.completedTheta B₁ f (B₁.period z).matrix) 0 (IntrinsicSplitTensor.Intrinsic.firstJacobi B₁ z u) := rfl

theorem splitKernel_product (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3) (z : Adelic.BallNatural.Ball) :
    IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂) z = fun ξ =>
      Adelic.DataTheta.completedTheta B₁ f₁ (B₁.period z).matrix (leftProjection (A := A) (S := S) ξ) *
      Adelic.DataTheta.completedTheta B₂ f₂ (B₂.period z).matrix (rightProjection (A := A) (S := S) ξ) := by
  funext ξ
  have hξ : Sum.elim (leftProjection (A := A) (S := S) ξ)
      (rightProjection (A := A) (S := S) ξ) = ξ := by
    funext i
    rcases i with i | i <;> rfl
  exact hξ ▸ IntrinsicBlockCompletion.Intrinsic.completed_blocks B₁ B₂ hΘ₁ hΘ₂ f₁ f₂ (B₁.period z) (B₂.period z)
    (leftProjection ξ) (rightProjection ξ)

theorem splitTensor_mixed (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3) (z : Adelic.BallNatural.Ball) (u v : IntrinsicExterior.Intrinsic.Tangent) :
    IntrinsicSplitTensor.Intrinsic.splitGeometricTensor B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂) z
      ![IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 0 u,
        IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 1 v] =
      (B₁.halfFrame z * B₂.halfFrame z)⁻¹ * ((2 : ℂ)⁻¹ *
        (fderiv ℂ (Adelic.DataTheta.completedTheta B₁ f₁ (B₁.period z).matrix) 0 (IntrinsicSplitTensor.Intrinsic.firstJacobi B₁ z u) *
          fderiv ℂ (Adelic.DataTheta.completedTheta B₂ f₂ (B₂.period z).matrix) 0 (IntrinsicSplitTensor.Intrinsic.firstJacobi B₂ z v))) := by
  rw [IntrinsicSplitTensor.Intrinsic.splitGeometricTensor_apply, IntrinsicSplitTensor.Intrinsic.splitJacobi_left, IntrinsicSplitTensor.Intrinsic.splitJacobi_right,
    splitKernel_product B₁ B₂ hΘ₁ hΘ₂]
  congr 2
  exact Calculus.mixed_hessian (leftProjection (A := A) (S := S))
    (rightProjection (A := A) (S := S)) _ _
    ((IntrinsicAnalysis.Intrinsic.completed_contDiff B₁ hE₁ hΘ₁ f₁ (B₁.period z)).of_le (by simp))
    ((IntrinsicAnalysis.Intrinsic.completed_contDiff B₂ hE₂ hΘ₂ f₂ (B₂.period z)).of_le (by simp))
    (Sum.elim (IntrinsicSplitTensor.Intrinsic.firstJacobi B₁ z u) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) → ℂ))
    (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) (IntrinsicSplitTensor.Intrinsic.firstJacobi B₂ z v)) rfl rfl

theorem splitTensor_mixed_reverse (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3) (z : Adelic.BallNatural.Ball) (u v : IntrinsicExterior.Intrinsic.Tangent) :
    IntrinsicSplitTensor.Intrinsic.splitGeometricTensor B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂) z
      ![IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 1 u,
        IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 0 v] =
      (B₁.halfFrame z * B₂.halfFrame z)⁻¹ * ((2 : ℂ)⁻¹ *
        (fderiv ℂ (Adelic.DataTheta.completedTheta B₁ f₁ (B₁.period z).matrix) 0 (IntrinsicSplitTensor.Intrinsic.firstJacobi B₁ z v) *
          fderiv ℂ (Adelic.DataTheta.completedTheta B₂ f₂ (B₂.period z).matrix) 0 (IntrinsicSplitTensor.Intrinsic.firstJacobi B₂ z u))) := by
  rw [IntrinsicSplitTensor.Intrinsic.splitGeometricTensor_apply, IntrinsicSplitTensor.Intrinsic.splitJacobi_right, IntrinsicSplitTensor.Intrinsic.splitJacobi_left,
    splitKernel_product B₁ B₂ hΘ₁ hΘ₂]
  apply congrArg (fun t : ℂ => (B₁.halfFrame z * B₂.halfFrame z)⁻¹ * ((2 : ℂ)⁻¹ * t))
  exact mixed_hessian_reverse (leftProjection (A := A) (S := S))
    (rightProjection (A := A) (S := S))
    (Adelic.DataTheta.completedTheta B₁ f₁ (B₁.period z).matrix) (Adelic.DataTheta.completedTheta B₂ f₂ (B₂.period z).matrix)
    ((IntrinsicAnalysis.Intrinsic.completed_contDiff B₁ hE₁ hΘ₁ f₁ (B₁.period z)).of_le (by simp))
    ((IntrinsicAnalysis.Intrinsic.completed_contDiff B₂ hE₂ hΘ₂ f₂ (B₂.period z)).of_le (by simp))
    (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) (IntrinsicSplitTensor.Intrinsic.firstJacobi B₂ z u))
    (Sum.elim (IntrinsicSplitTensor.Intrinsic.firstJacobi B₁ z v) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) → ℂ)) rfl rfl

theorem splitTopForm_product (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3) (z : Adelic.BallNatural.Ball) :
    IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂) z =
      IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ f₁ z)
        (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₂ f₂ z) := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
  rw [hw]
  unfold IntrinsicSplitTensor.Intrinsic.splitTopForm
  rw [IntrinsicSecondProjection.Intrinsic.secondProjection_apply, IntrinsicExterior.Intrinsic.wedge_apply]
  rw [splitTensor_mixed B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂,
    splitTensor_mixed B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂,
    splitTensor_mixed_reverse B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂,
    splitTensor_mixed_reverse B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂]
  simp only [thetaOneForm_apply_jacobi, mul_inv_rev]
  ring

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitWedge.Intrinsic
