import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.LocalLog
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationCurvature
import OAI.Analysis.DifferentialForms.Manifold.DegreeZero

/-! # Frame Curvature -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual exterior derivative of the algebraic theta-frame
connection equals the original Gaussian curvature on every frame
domain. Local holomorphic logarithms provide the exact primitives. -/

open OAI.Analysis.DifferentialForms.Manifold.DegreeZero Set Filter _root_.Topology
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))

def Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnectionRaw (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Basic.RawForm (Reference.Fiber.ReferenceTangent s) 1 := fun w =>
  let dq : Reference.Fiber.ReferenceTangent s →L[ℝ] ℂ := (fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w).restrictScalars ℝ
  ContinuousAlternatingMap.ofSubsingleton ℝ (Reference.Fiber.ReferenceTangent s) ℂ (0 : Fin 1)
    (RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form w + (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w)⁻¹ • dq)

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnectionRaw_apply
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : Reference.Fiber.ReferenceTangent s)
    (v : Fin 1 → Reference.Fiber.ReferenceTangent s) :
    F.thetaFrameConnectionRaw hP U V i w v = F.thetaFrameConnection hP U V i w (v 0) := rfl

def Reference.Fiber.ReferenceAnalyticFiber.thetaLogZeroForm (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w₀ : F.periodData.space) : Analysis.DifferentialForms.Manifold.Basic.RawForm (Reference.Fiber.ReferenceTangent s) 0 := fun w =>
  ContinuousAlternatingMap.constOfIsEmpty ℝ (Reference.Fiber.ReferenceTangent s) (Fin 0) (F.thetaLocalLog hP U V i w₀ w)

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaLogZeroForm_contDiffAt
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w₀ w : F.periodData.space)
    (hw : w ∈ F.thetaLogDomain hP U V i w₀) :
    ContDiffAt ℝ ∞ (F.thetaLogZeroForm hP U V i w₀) w := by
  have h : ContDiffAt ℝ ∞ (F.thetaLocalLog hP U V i w₀) w :=
    (F.thetaLocalLog_contDiffAt hP U V i w₀ w hw).restrict_scalars ℝ
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Reference.Fiber.ReferenceTangent s) ℂ (Fin 0)).contDiff.contDiffAt.comp w h

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnectionRaw_local
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w₀ : F.periodData.space)
    (h₀ : w₀ ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    F.thetaFrameConnectionRaw hP U V i =ᶠ[𝓝 w₀]
      (fun w => RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.form w + extDeriv (F.thetaLogZeroForm hP U V i w₀) w) := by
  have hm := F.mem_thetaLogDomain hP U V i w₀ h₀
  filter_upwards [(F.thetaLogDomain_isOpen hP U V i w₀).mem_nhds hm] with w hw
  ext v
  refine (F.thetaFrameConnectionRaw_apply hP U V i w v).trans ?_
  have hreal := ((F.thetaLocalLog_contDiffAt hP U V i w₀ w hw).differentiableAt (by simp)).fderiv_restrictScalars ℝ
  have hd : extDeriv (F.thetaLogZeroForm hP U V i w₀) w v =
      fderiv ℂ (F.thetaLocalLog hP U V i w₀) w (v 0) := by
    exact (congrArg (fun t : Analysis.DifferentialForms.Manifold.Basic.FormValue (Reference.Fiber.ReferenceTangent s) 1 => t v)
      (extDeriv_constOfIsEmpty (𝕜 := ℝ)
        (fun x : Reference.Fiber.ReferenceTangent s => F.thetaLocalLog hP U V i w₀ x) w)).trans
      (congrArg (fun d : F.periodData.space →L[ℝ] ℂ => d (v 0)) hreal)
  exact (F.thetaFrameConnection_local_log hP U V i w₀ w (v 0) h₀ hw).trans
    (congrArg (fun c : ℂ => RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.form w (v 0) + c) hd.symm)

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnectionRaw_curvature
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : F.periodData.space)
    (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    extDeriv (F.thetaFrameConnectionRaw hP U V i) w = F.referenceCurvature w := by
  have hlog := F.thetaLogZeroForm_contDiffAt hP U V i w w (F.mem_thetaLogDomain hP U V i w hw)
  have hdlog : ContDiffAt ℝ ∞ (extDeriv (F.thetaLogZeroForm hP U V i w)) w :=
    Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffAt_extDeriv_of_add_one_le hlog (by simp)
  refine (F.thetaFrameConnectionRaw_local hP U V i w hw).extDeriv_eq.trans ?_
  have hsum := extDeriv_fun_add
    ((RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.form).smooth.differentiable (by simp) w)
    (hdlog.differentiableAt (by simp))
  exact hsum.trans ((congrArg
    (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue (Reference.Fiber.ReferenceTangent s) 2 => extDeriv (RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.form) w + a)
    (Analysis.DifferentialForms.Manifold.SquareZero.extDeriv_extDeriv_of_contDiffAt hlog)).trans (add_zero _))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
