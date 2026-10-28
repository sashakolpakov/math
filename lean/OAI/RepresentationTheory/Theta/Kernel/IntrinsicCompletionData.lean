import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianFixedLevel
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPrerequisites
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicOne

/-! # Intrinsic Completion Data -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompletionData.Intrinsic

noncomputable section

/-! Native ThetaKernel conclusion data: actual completed tensors and finite
transport, an explicit determinant constant, and one principal level
supporting both the native wedge factors and the C-infinity Lagrangian family. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSubspaces.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianFixedLevel.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLevelSmoothTop.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.IntrinsicDescent OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {hd : d ≠ 0} {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁}
variable {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hd P₁ A)
variable (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hd P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))
variable (Q : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S),
  IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicCompactChoices.Intrinsic.choiceArithmetic (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) p))

def CompactTensorTransport : Prop :=
  ∀ (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6),
    ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F 6,
      (∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p Q₀.comparison (Q p).comparison) x *
          Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) ∧
      ∀ (a : ℕ) (z : Adelic.BallNatural.Ball),
        ((Q p).comparison.halfFrame IntrinsicBallTopology.Intrinsic.origin / Q₀.comparison.halfFrame IntrinsicBallTopology.Intrinsic.origin) •
          Adelic.DataTheta.geometricTensor (Q p).comparison g a z =
            IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTensor Q₀.comparison f a (IntrinsicCompactActionParameter.Intrinsic.actionParameter (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) p,z.val)

variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (hQ : ∀ p, IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ)
variable (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))

def NativeCommonLevelConclusion (c : ℂˣ) : Prop :=
  ∀ (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F 6)) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H)) (N₀ : ℕ), 0 < N₀ →
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L,
          Adelic.FiniteSchwartz.finiteAction F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd Q₀.characters (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) Q₀.splittings g f = f) ∧
        ∃ (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit Q₀.comparison N z w),
          CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧ SecondCountableTopology (Quotient R) ∧
          ∀ f ∈ Φ, IntrinsicDeterminantFactorization.IntrinsicDescent.NativeFactorizationAtLevel Q₁ Q₂ Q₀.comparison c L f ∧
            ∃ family : IntrinsicCompactSubspaces.Intrinsic.CompactLagrangianChoice (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → IntrinsicLevelSmoothTop.Intrinsic.LevelSmoothTop Q₀.comparison N,
              Continuous family ∧
              (∀ p, (family p).val = IntrinsicLagrangianFixedLevel.Intrinsic.nativeLagrangianFamily Q₀ Q ψ h₀ hQ hE f p) ∧
              (∀ z, (family (Quotient.mk (IntrinsicCompactSubspaces.Intrinsic.compactSubspaceSetoid (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))
                (IntrinsicCompactChoices.Intrinsic.identityChoice (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))).val.value z = IntrinsicSecondProjection.Intrinsic.thetaTopForm Q₀.comparison f z) ∧
              ∀ p, ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle Q₀.comparison N,
                Continuous descended ∧ (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection Q₀.comparison N R hR (descended q) = q) ∧
                ∀ z, descended (Quotient.mk R z) =
                  Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit Q₀.comparison N) (z,(family p).val.value z)

def NativeConclusion : Prop :=
  ∃ c : ℂˣ,
    (c : ℂ) = (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio Q₁.comparison Q₂.comparison Q₀.comparison IntrinsicBallTopology.Intrinsic.origin)⁻¹ ∧
    (c : ℂ) ^ 2 = LinearMap.det (IntrinsicDeterminantComparison.Intrinsic.frameComparison Q₁.comparison Q₂.comparison Q₀.comparison) ∧
    (∀ z, Q₀.comparison.halfFrame z * (c : ℂ) =
      Q₁.comparison.halfFrame z * Q₂.comparison.halfFrame z) ∧
    (∀ z : Adelic.BallNatural.Ball, ∃ f : Adelic.FiniteSchwartz.finiteSchwartz F 6, IntrinsicSecondProjection.Intrinsic.thetaTopForm Q₀.comparison f z ≠ 0) ∧
    CompactTensorTransport Q₀ Q ∧ NativeCommonLevelConclusion Q₁ Q₂ Q₀ Q ψ h₀ hQ hE c

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompletionData.Intrinsic
