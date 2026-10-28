import OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitRegularity

/-! # Intrinsic Fixed Factorization -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedFactorization.Intrinsic

noncomputable section

/-! Native fixed-splitting factorization and nonvanishing. The total top form
is compared with wedges of the intrinsic theta one-forms; the finite input
transform and the scalar factor are both constructed. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitRegularity.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison OAI.RepresentationTheory.Theta.Kernel.IntrinsicComparison.IntrinsicKernel
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem native_top_comparison
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f g : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hweight : ∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) (z : Adelic.BallNatural.Ball) :
    IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z = (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio B₁ B₂ B IntrinsicBallTopology.Intrinsic.origin)⁻¹ • IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ g z := by
  unfold IntrinsicSecondProjection.Intrinsic.thetaTopForm IntrinsicSplitTensor.Intrinsic.splitTopForm
  rw [IntrinsicTensorComparison.Intrinsic.native_tensor_comparison B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG
    hE₁ hE₂ hE hTensorDecomposition hΘ₁ hΘ₂ hΘ f g hweight z, map_smul,
    IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio_constant B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z]

theorem native_fixed_factorization
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) :
    ∃ c : ℂˣ,
      (∀ f : Adelic.FiniteSchwartz.finiteSchwartz F 6, ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F 6,
        (∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
          IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
            Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) ∧
        ∃ (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3),
          (∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 g x =
            ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) x) ∧
          ∀ z : Adelic.BallNatural.Ball, IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z =
            ∑ j, (c : ℂ) • IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ (a j) z)
              (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₂ (b j) z)) ∧
      ∀ z : Adelic.BallNatural.Ball, ∃ f : Adelic.FiniteSchwartz.finiteSchwartz F 6, IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z ≠ 0 := by
  let c : ℂˣ := Units.mk0 (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio B₁ B₂ B IntrinsicBallTopology.Intrinsic.origin)⁻¹
    (inv_ne_zero (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio_nonzero B₁ B₂ B hG₁ hG₂ hG IntrinsicBallTopology.Intrinsic.origin))
  refine ⟨c,?_,?_⟩
  · intro f
    obtain ⟨g,hg⟩ := IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 f (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B)
    obtain ⟨n,a,b,he,hform⟩ := IntrinsicSplitFactorization.Intrinsic.finite_wedge_factorization B₁ B₂ hE₁ hE₂ hTensorDecomposition hΘ₁ hΘ₂ g
    refine ⟨g,hg,n,a,b,he,?_⟩
    intro z
    rw [native_top_comparison B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG
      hE₁ hE₂ hE hTensorDecomposition hΘ₁ hΘ₂ hΘ f g hg z, hform, Finset.smul_sum]
    rfl
  · intro z
    obtain ⟨g,hg⟩ := IntrinsicSplitRegularity.Intrinsic.splitTopForm_nonzero B₁ B₂ hE₁ hE₂ hG₁ hG₂ hΘ₁ hΘ₂ z
    obtain ⟨f,hf⟩ := IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 g (IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B)
    have hweight (x : Fin 6 → F) : Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
          Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
      rw [hf, ← mul_assoc, IntrinsicComparison.IntrinsicKernel.quadraticPhase_neg_mul, one_mul]
    refine ⟨f,?_⟩
    rw [native_top_comparison B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG
      hE₁ hE₂ hE hTensorDecomposition hΘ₁ hΘ₂ hΘ f g hweight z]
    exact smul_ne_zero (inv_ne_zero (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio_nonzero B₁ B₂ B hG₁ hG₂ hG IntrinsicBallTopology.Intrinsic.origin)) hg

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedFactorization.Intrinsic
