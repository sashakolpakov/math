import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit

/-! # Intrinsic Split Tensor -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic

noncomputable section

/-! The completed order-two tensor in the explicitly constructed split
period, determinant frame, and Hodge coordinates. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))

def splitKernel (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) :
    (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) → ℂ) → ℂ :=
  IntrinsicBlockCompletion.IntrinsicKernel.literalCompleted (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition) f
    (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z))

def splitJacobi (z : Adelic.BallNatural.Ball) : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) →L[ℂ]
    (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) → ℂ) :=
  (Matrix.toLin' (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).invᵀ).toContinuousLinearMap.comp
    (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S).toContinuousLinearMap

def splitGeometricTensor (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) :
    Adelic.DataTheta.TaylorTensor (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 2 :=
  (B₁.halfFrame z * B₂.halfFrame z)⁻¹ •
    (((2 : ℂ)⁻¹) • iteratedFDeriv ℂ 2 (splitKernel B₁ B₂ f z) 0).compContinuousLinearMap
      (fun _ => splitJacobi B₁ B₂ z)

def splitTopForm (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) : IntrinsicExterior.Intrinsic.TopCovector :=
  IntrinsicSecondProjection.Intrinsic.secondProjection (splitGeometricTensor B₁ B₂ f z)

def firstJacobi (z : Adelic.BallNatural.Ball) (u : IntrinsicExterior.Intrinsic.Tangent) : Adelic.BallGeometryData.FrameIndex A → ℂ :=
  (B₁.frame z).invᵀ.mulVec (OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A) u)

theorem splitJacobi_left (z : Adelic.BallNatural.Ball) (u : IntrinsicExterior.Intrinsic.Tangent) :
    splitJacobi B₁ B₂ z (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 0 u) =
      Sum.elim (firstJacobi B₁ z u) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) → ℂ) := by
  change (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).invᵀ.mulVec
    (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 0 u)) = _
  rw [IntrinsicHodgeSplit.Intrinsic.split_slot_left]
  simpa only [Matrix.mulVec_zero, firstJacobi] using
    IntrinsicBlockSiegel.Intrinsic.blockFrame_invTranspose_mulVec (B₁.frame z) (B₂.frame z)
      (OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A) u) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) → ℂ)

theorem splitJacobi_right (z : Adelic.BallNatural.Ball) (u : IntrinsicExterior.Intrinsic.Tangent) :
    splitJacobi B₁ B₂ z (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 1 u) =
      Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) (firstJacobi B₂ z u) := by
  change (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).invᵀ.mulVec
    (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 1 u)) = _
  rw [IntrinsicHodgeSplit.Intrinsic.split_slot_right]
  simpa only [Matrix.mulVec_zero, firstJacobi] using
    IntrinsicBlockSiegel.Intrinsic.blockFrame_invTranspose_mulVec (B₁.frame z) (B₂.frame z) (0 : Adelic.BallGeometryData.FrameIndex A → ℂ)
      (OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) u)

theorem splitGeometricTensor_apply (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball)
    (u v : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    splitGeometricTensor B₁ B₂ f z ![u,v] =
      (B₁.halfFrame z * B₂.halfFrame z)⁻¹ * ((2 : ℂ)⁻¹ *
        iteratedFDeriv ℂ 2 (splitKernel B₁ B₂ f z) 0
          ![splitJacobi B₁ B₂ z u, splitJacobi B₁ B₂ z v]) := by
  change (B₁.halfFrame z * B₂.halfFrame z)⁻¹ * ((2 : ℂ)⁻¹ *
    iteratedFDeriv ℂ 2 (splitKernel B₁ B₂ f z) 0
      (fun i => splitJacobi B₁ B₂ z (![u,v] i))) = _
  have he : (fun i : Fin 2 => splitJacobi B₁ B₂ z (![u,v] i)) =
      ![splitJacobi B₁ B₂ z u, splitJacobi B₁ B₂ z v] := by
    funext i
    fin_cases i <;> rfl
  rw [he]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic
