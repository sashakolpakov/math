import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LogarithmicConnectionChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.TorusConnection

/-! # Logarithmic Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The theta-frame connection satisfies its actual logarithmic change
law after every differentiable vector-coordinate map. -/

open Filter _root_.Topology

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaConnection_logarithmic_change
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (L : A → F.periodData.space) (l : A → ℂ) (x v : A)
    (hL : DifferentiableAt ℂ L x) (hl : DifferentiableAt ℂ l x)
    (hi : L x ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) (hj : L x ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V j)
    (he : (fun y => Complex.exp (l y)) =ᶠ[𝓝 x]
      (fun y => RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 (L y) / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 (L y))) :
    F.thetaFrameConnection hP U V j (L x) (fderiv ℂ L x v) -
      F.thetaFrameConnection hP U V i (L x) (fderiv ℂ L x v) = fderiv ℂ l x v := by
  have hqi : DifferentiableAt ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) (L x) :=
    RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt U V i.1 i.2 (L x) hi.1
  have hqj : DifferentiableAt ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2) (L x) :=
    RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt U V j.1 j.2 (L x) hj.1
  have h := LogarithmicConnectionChange.logarithmicDerivative_ratio_log
    (fun y => RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 (L y))
    (fun y => RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 (L y)) l x v (hqi.comp x hL) hl
    (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 (L x) hi.1 hi.2) he
  have hDi : fderiv ℂ (fun y => RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 (L y)) x v =
      fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) (L x) (fderiv ℂ L x v) :=
    congrArg (fun d : A →L[ℂ] ℂ => d v) (fderiv_comp x hqi hL)
  have hDj : fderiv ℂ (fun y => RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 (L y)) x v =
      fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2) (L x) (fderiv ℂ L x v) :=
    congrArg (fun d : A →L[ℂ] ℂ => d v) (fderiv_comp x hqj hL)
  rw [hDi, hDj] at h
  unfold Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnection
  linear_combination h

variable [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A]

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaConnectionRaw_logarithmic_change
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (L : A → F.periodData.space) (l : A → ℂ) (x : A)
    (hL : DifferentiableAt ℂ L x) (hl : DifferentiableAt ℂ l x)
    (hi : L x ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) (hj : L x ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V j)
    (he : (fun y => Complex.exp (l y)) =ᶠ[𝓝 x]
      (fun y => RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 (L y) / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 (L y))) :
    (F.thetaTorusConnectionCoefficients hP U V j (L x)).compContinuousLinearMap (fderiv ℝ L x) -
      (F.thetaTorusConnectionCoefficients hP U V i (L x)).compContinuousLinearMap (fderiv ℝ L x) =
        extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ A (Fin 0) (l y)) x := by
  ext v
  have hreal := hL.fderiv_restrictScalars ℝ
  have hvalue : fderiv ℝ L x (v 0) = fderiv ℂ L x (v 0) :=
    congrArg (fun d : A →L[ℝ] F.periodData.space => d (v 0)) hreal
  change F.thetaFrameConnection hP U V j (L x) (fderiv ℝ L x (v 0)) -
    F.thetaFrameConnection hP U V i (L x) (fderiv ℝ L x (v 0)) = _
  rw [hvalue]
  refine (F.thetaConnection_logarithmic_change hP U V i j L l x (v 0) hL hl hi hj he).trans ?_
  have hzero := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue A 1 => a v) (extDeriv_constOfIsEmpty (𝕜 := ℝ) l x)
  exact (congrArg (fun d : A →L[ℝ] ℂ => d (v 0)) (hl.fderiv_restrictScalars ℝ)).symm.trans hzero.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
