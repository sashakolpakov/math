import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompletionData

/-! # Intrinsic Core -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCore.Intrinsic

noncomputable section

/-! The intrinsic theta-kernel statement packages the complete cotangent,
derivative, tensor-decomposition, one-form, and adelic-theta prerequisites.
Its witnesses carry the corresponding native validity conclusions. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.Data
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompletionData.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPrerequisites.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicOne.Intrinsic

def Statement : Prop :=
  ∀ (_hCotangentBundle : IntrinsicPrerequisites.Intrinsic.CotangentBundleStatement.{0, 0})
    (_hDerivativeFactorization : IntrinsicPrerequisites.Intrinsic.DerivativeFactorizationStatement.{0, 0, 0, 0, 0, 0, 0, 0, 0})
    (_hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (_hThetaOneForms : IntrinsicOne.Intrinsic.NativeThetaOneFormsStatement) (_hAdelicTheta : Adelic.Data.CompleteStatement)
    (F : Type) [Field F] [NumberField F] (d : F) (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (_hHermitian : H.val.conjTranspose = H.val) (_hSkewHermitian : K₁.val.conjTranspose = -K₁.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (_hContinuous : Continuous ψ) (_hUnitNorm : ∀ x, ‖ψ x‖ = 1)
    (_hNontrivial : ∃ x, ψ x ≠ 1) (_hTrivialOnField : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : IntrinsicSplitting.IntrinsicSummands.SecondLine A)
    (P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁) (P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form)
    (_hArchimedean : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ)
    (_hFirstGaussian : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (_hSecondGaussian : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (h_GaussianConvergence : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))),
    ∃ (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hq.1 P₁ A)
      (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hq.1 P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
      (Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hq.1 (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))
      (Q : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S),
        IntrinsicCompactChoices.Intrinsic.TotalWitnesses hq.1 (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicCompactChoices.Intrinsic.choiceArithmetic (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) p)),
      IntrinsicSplitting.IntrinsicSummands.SummandValid Q₁ ψ ∧ IntrinsicSplitting.IntrinsicSummands.SummandValid Q₂ ψ ∧
      ∃ (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (hQ : ∀ p, IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ),
        IntrinsicCompletionData.Intrinsic.NativeConclusion Q₁ Q₂ Q₀ Q ψ h₀ hQ h_GaussianConvergence

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCore.Intrinsic
