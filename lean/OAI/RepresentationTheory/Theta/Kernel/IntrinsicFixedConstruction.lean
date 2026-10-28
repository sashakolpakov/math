import OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices

/-! # Intrinsic Fixed Construction -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedConstruction.IntrinsicConstruction

noncomputable section

/-! Starting from complete adelic theta data, retain every summand and total
validity conclusion while deriving the wedge factorization and nonzero total
form. The compact-place continuity assertion remains a separate obligation. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.Data
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.IntrinsicSecondConstruction
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedFactorization.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {hd : d ≠ 0} {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}

def FixedFactorizationConclusion
    (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hd P₁ A)
    (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hd P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
    (Q : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) : Prop :=
  ∃ c : ℂˣ,
    (∀ f : Adelic.FiniteSchwartz.finiteSchwartz F 6, ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F 6,
      (∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear Q₁.comparison Q₂.comparison Q.comparison) x *
          Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) ∧
      ∃ (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3),
        (∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 g x =
          ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 (a j) (b j)) x) ∧
        ∀ z : Adelic.BallNatural.Ball, IntrinsicSecondProjection.Intrinsic.thetaTopForm Q.comparison f z =
          ∑ j, (c : ℂ) • IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a j) z)
            (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b j) z)) ∧
    ∀ z : Adelic.BallNatural.Ball, ∃ f : Adelic.FiniteSchwartz.finiteSchwartz F 6, IntrinsicSecondProjection.Intrinsic.thetaTopForm Q.comparison f z ≠ 0

theorem construct_native_fixed_factorization (h_AdelicTheta : Adelic.Data.CompleteStatement)
    (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK₁ : K₁.val.conjTranspose = -K₁.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hn : ∃ x, ψ x ≠ 1) (hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : IntrinsicSplitting.IntrinsicSummands.SecondLine A)
    (P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁) (P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form)
    (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0}) :
    ∃ (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hq.1 P₁ A)
      (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hq.1 P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
      (Q : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hq.1 (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)),
      IntrinsicSplitting.IntrinsicSummands.SummandValid Q₁ ψ ∧ IntrinsicSplitting.IntrinsicSummands.SummandValid Q₂ ψ ∧ IntrinsicCompactChoices.Intrinsic.TotalValid Q ψ ∧ FixedFactorizationConclusion Q₁ Q₂ Q := by
  obtain ⟨Q₁,Q₂,h₁,h₂,_⟩ := IntrinsicSplitting.IntrinsicSummands.construct_two_summands h_AdelicTheta hq hH hK₁ ψ hc hu hn hp A S P₁ P₂ hArch
  obtain ⟨C,hψ,hChar,D,hAd,hFin,B,hCoord,hGeom,hOsc,hBranch,hUnique,hTheta,hCov,hDesc,_,_,hTop⟩ :=
    IntrinsicCompactChoices.IntrinsicSecondConstruction.construct_total h_AdelicTheta hq hH (IntrinsicSplitting.IntrinsicArithmetic.blockUnit_skewHermitian S.form hK₁ S.skewHermitian)
      ψ hc hu hn hp (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) hArch
  refine ⟨Q₁,Q₂,⟨C,D,B⟩,h₁,h₂,⟨hψ,hChar,hAd,hFin,hCoord,hGeom,hOsc,hBranch,hUnique,hTheta,hCov,hDesc,hTop⟩,?_⟩
  obtain ⟨_,_,_,_,hC₁,hG₁,_,_,_,hΘ₁,_,_,_⟩ := h₁
  obtain ⟨_,_,_,_,hC₂,hG₂,_,_,_,hΘ₂,_,_,_⟩ := h₂
  exact IntrinsicFixedFactorization.Intrinsic.native_fixed_factorization Q₁.comparison Q₂.comparison B hC₁ hC₂ hCoord hG₁ hG₂ hGeom
    hE₁ hE₂ hE hTensorDecomposition hΘ₁ hΘ₂ hTheta

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedConstruction.IntrinsicConstruction
