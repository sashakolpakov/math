import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitWedge
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSummability
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicDecomposition

/-! # Intrinsic Split Factorization -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization.Intrinsic

noncomputable section

/-! Every actual finite Schwartz input has a finite wedge expansion in
the constructed split coordinates. No tensor-factorization hypothesis
about that input is added. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicDecomposition.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSummability.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitWedge.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis.Intrinsic

variable {F : Type} [Field F] [NumberField F]

theorem input_products (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    ∃ (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3),
      ∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 f x =
        ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) x := by
  obtain ⟨n,c,a,b,heval⟩ := IntrinsicDecomposition.Intrinsic.finite_tensor_expansion F hTensorDecomposition 3 f
  refine ⟨n, (fun j => c j • a j), b, ?_⟩
  intro x
  rw [heval]
  apply Finset.sum_congr rfl
  intro j _
  rw [IntrinsicSchwartz.Intrinsic.productInput_value F 3 3]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

variable {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))

theorem splitKernel_finite_sum (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3)
    (heval : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 f x =
      ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) x)
    (z : Adelic.BallNatural.Ball) : IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ f z =
      fun ξ => ∑ j, IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) z ξ := by
  funext ξ
  have hb : IntrinsicBlockCompletion.IntrinsicKernel.literalTheta (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition) f
      (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix ξ =
      ∑ j, IntrinsicBlockCompletion.IntrinsicKernel.literalTheta (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition)
        (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j))
        (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix ξ := by
    simp only [IntrinsicBlockCompletion.IntrinsicKernel.literalTheta, heval, Finset.sum_mul]
    exact Summable.tsum_finsetSum (fun j _ =>
      IntrinsicBlockSummability.Intrinsic.product_summable B₁ B₂ hΘ₁ hΘ₂ (a j) (b j) (B₁.period z) (B₂.period z) ξ)
  simp only [IntrinsicSplitTensor.Intrinsic.splitKernel, IntrinsicBlockCompletion.IntrinsicKernel.literalCompleted, hb, Finset.mul_sum]

theorem splitKernel_product_contDiff (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3) (z : Adelic.BallNatural.Ball) :
    ContDiff ℂ ⊤ (IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂) z) := by
  rw [IntrinsicSplitWedge.Intrinsic.splitKernel_product B₁ B₂ hΘ₁ hΘ₂]
  exact ((IntrinsicAnalysis.Intrinsic.completed_contDiff B₁ hE₁ hΘ₁ f₁ (B₁.period z)).comp
    (IntrinsicSplitWedge.Intrinsic.leftProjection (A := A) (S := S)).contDiff).mul
      ((IntrinsicAnalysis.Intrinsic.completed_contDiff B₂ hE₂ hΘ₂ f₂ (B₂.period z)).comp
        (IntrinsicSplitWedge.Intrinsic.rightProjection (A := A) (S := S)).contDiff)

theorem splitTensor_finite_sum (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3)
    (heval : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 f x =
      ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) x)
    (z : Adelic.BallNatural.Ball) : IntrinsicSplitTensor.Intrinsic.splitGeometricTensor B₁ B₂ f z =
      ∑ j, IntrinsicSplitTensor.Intrinsic.splitGeometricTensor B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) z := by
  unfold IntrinsicSplitTensor.Intrinsic.splitGeometricTensor
  rw [splitKernel_finite_sum B₁ B₂ hΘ₁ hΘ₂ f n a b heval z,
    iteratedFDeriv_fun_sum_apply (fun j _ =>
      ((splitKernel_product_contDiff B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂ (a j) (b j) z).of_le
        (show (2 : ℕ∞ω) ≤ ⊤ from le_top)).contDiffAt)]
  apply ContinuousMultilinearMap.ext
  intro v
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, Finset.mul_sum]

theorem splitTop_finite_sum (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3)
    (heval : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 f x =
      ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) x)
    (z : Adelic.BallNatural.Ball) : IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ f z =
      ∑ j, IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) z := by
  unfold IntrinsicSplitTensor.Intrinsic.splitTopForm
  rw [splitTensor_finite_sum B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂ f n a b heval z, map_sum]

theorem finite_wedge_factorization (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    ∃ (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3),
      (∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 f x =
        ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) x) ∧
      ∀ z : Adelic.BallNatural.Ball, IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ f z =
        ∑ j, IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ (a j) z)
          (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₂ (b j) z) := by
  obtain ⟨n,a,b,heval⟩ := input_products hTensorDecomposition f
  refine ⟨n,a,b,heval,?_⟩
  intro z
  rw [splitTop_finite_sum B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂ f n a b heval z]
  apply Finset.sum_congr rfl
  intro j _
  exact IntrinsicSplitWedge.Intrinsic.splitTopForm_product B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂ (a j) (b j) z

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization.Intrinsic
