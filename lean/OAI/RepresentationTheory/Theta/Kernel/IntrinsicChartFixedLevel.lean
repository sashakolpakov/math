import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualDifferenceOperator
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactTensorMatch

/-! # Intrinsic Chart Fixed Level -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartFixedLevel.Intrinsic

noncomputable section

/-! The explicit continuous compact chart top forms are invariant at
the original native finite level. The exact finite phase transport is
implemented by commuting actual residual Schwartz operators. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactTensorMatch.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualDifferenceOperator.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.LinearOperatorFixedLevel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicOriginNormalizedDescent.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P A) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
variable (Qp : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

theorem normalized_chart_top_invariant
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ)
    (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (hp : IntrinsicCompactChoices.Intrinsic.TotalValid Qp ψ)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hfix : Adelic.FiniteSchwartz.finiteAction F H K hd Q₀.characters P Q₀.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f = f)
    (z : Adelic.BallNatural.Ball) :
    (IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop Q₀.comparison f
      (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,(Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z).val)).compContinuousLinearMap
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
          (Adelic.BallNatural.asSL (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) =
      IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop Q₀.comparison f (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) := by
  obtain ⟨hψ₀,_,_,_,hC₀,hG₀,hO₀,_,hU₀,hΘ₀,_,_,_⟩ := h₀
  obtain ⟨hψp,_,_,_,hCp,hGp,hOp,_,hUp,hΘp,hCovp,_,_⟩ := hp
  have harch₀ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) Q₀.characters.ψ := by rw [hψ₀]; exact hArch
  have harchp : Adelic.DataTheta.Descent.StandardArchCharacter (A := IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) Qp.characters.ψ := by
    rw [hψp]
    exact hArch
  let L := IntrinsicResidualDifferenceOperator.Intrinsic.residualDifferenceOperator p Q₀.comparison Qp.comparison hC₀ hG₀ hO₀ hCp hGp hOp
  have hL := IntrinsicResidualDifferenceOperator.Intrinsic.residual_difference_commutes p Q₀.comparison Qp.comparison hC₀ hG₀ hO₀ hCp hGp hOp
    harch₀ harchp (hψp.trans hψ₀.symm) hU₀ hUp
  obtain ⟨f',hw,he⟩ := IntrinsicCompactTensorMatch.Intrinsic.compact_normalized_top_transport p Q₀.comparison Qp.comparison
    hC₀ hCp hG₀ hGp hE hΘ₀ hΘp f
  have ht (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) : Adelic.ThetaEvaluation.theta F 6 (L φ) f = Adelic.ThetaEvaluation.theta F 6 φ f' :=
    LinearOperatorFixedLevel.Intrinsic.linear_operator_theta_weights F (m := 2) L
      (IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p Q₀.comparison Qp.comparison))
      (IntrinsicResidualDifferenceOperator.Intrinsic.residual_difference_rational_value p Q₀.comparison Qp.comparison hC₀ hG₀ hO₀ hCp hGp hOp
        harch₀ harchp) f f' hw φ
  have ht₀ (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) :
      Adelic.ThetaEvaluation.theta F 6 φ (Adelic.FiniteSchwartz.finiteAction F H K hd Q₀.characters P Q₀.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f') =
        Adelic.ThetaEvaluation.theta F 6 φ f' :=
    LinearOperatorFixedLevel.Intrinsic.finite_action_theta_of_linear_operator F H K hd P Q₀.characters Q₀.splittings
      hns hH hK L hL f f' ht g hfix φ
  have htp (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) :
      Adelic.ThetaEvaluation.theta F 6 φ (Adelic.FiniteSchwartz.finiteAction F H K hd Qp.characters P Qp.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f') =
        Adelic.ThetaEvaluation.theta F 6 φ f' :=
    (IntrinsicArchimedeanIndependence.Intrinsic.finite_action_theta_independent F H K hd P Q₀.characters Qp.characters Q₀.splittings Qp.splittings
      hns hH hK (hψp.trans hψ₀.symm) hU₀ g φ f').trans (ht₀ φ)
  have htop := LinearOperatorFixedLevel.Intrinsic.theta_top_of_theta_fixed F H hd Qp.comparison P Qp.characters Qp.splittings
    hGp hΘp hCovp g f' htp z
  have hball : Qp.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) =
      Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) := by
    apply Subtype.ext
    apply Units.ext
    exact (hGp.2.1 _).trans (hG₀.2.1 _).symm
  rw [hball] at htop
  have hn : (IntrinsicOriginNormalizedDescent.Intrinsic.originNormalizedTop Q₀.comparison p Qp.comparison f'
      (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
          (Adelic.BallNatural.asSL (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) =
      IntrinsicOriginNormalizedDescent.Intrinsic.originNormalizedTop Q₀.comparison p Qp.comparison f' z := by
    ext a
    exact congrArg (fun η : IntrinsicExterior.Intrinsic.TopCovector =>
      (Qp.comparison.halfFrame IntrinsicBallTopology.Intrinsic.origin / Q₀.comparison.halfFrame IntrinsicBallTopology.Intrinsic.origin) * η a) htop
  rw [he,he] at hn
  exact hn

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartFixedLevel.Intrinsic
