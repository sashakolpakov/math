import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Connection
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Local Log -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalLog.Geometric

noncomputable section

/-! Actual local holomorphic logarithms of the consecutive theta gauge
give local potentials for the algebraic theta-frame connection. -/

open Set Filter _root_.Topology
open scoped ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))

theorem thetaGauge_contDiffAt
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hi : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) : ContDiffAt ℂ ∞ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w := by
  have ho := RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_isOpen U V i
  have hd : DifferentiableOn ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) (RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :=
    fun x hx => (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt U V i.1 i.2 x hx.1).differentiableWithinAt
  exact (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    ho hd w hi).contDiffAt (ho.mem_nhds hi)

def thetaLogDomain (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w₀ : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) : Set (ProjectivePeriodData.Geometric.projectivePeriodData F).space :=
  RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i ∩ interior {w | RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w /
    RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀ ∈ Complex.slitPlane}

theorem thetaLogDomain_isOpen (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w₀ : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) : IsOpen ((thetaLogDomain F) hP U V i w₀) :=
  (RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_isOpen U V i).inter isOpen_interior

theorem mem_thetaLogDomain (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w₀ : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (hi : w₀ ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    w₀ ∈ (thetaLogDomain F) hP U V i w₀ := by
  have hq := RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 w₀ hi.1 hi.2
  have hs : RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀ / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀ ∈ Complex.slitPlane := by
    simpa only [div_self hq] using Complex.one_mem_slitPlane
  refine ⟨hi, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact (((thetaGauge_contDiffAt F) hP U V i w₀ hi).continuousAt.div_const _).eventually
    (Complex.isOpen_slitPlane.mem_nhds hs)

def thetaLocalLog (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w₀ w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) : ℂ :=
  Complex.log (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀) +
    Complex.log (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀)

theorem thetaLocalLog_contDiffAt
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w₀ w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hw : w ∈ (thetaLogDomain F) hP U V i w₀) : ContDiffAt ℂ ∞ ((thetaLocalLog F) hP U V i w₀) w := by
  have hs : RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀ ∈ Complex.slitPlane :=
    (interior_subset : interior {x | RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 x /
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀ ∈ Complex.slitPlane} ⊆ _) hw.2
  exact ((Complex.contDiffAt_log hs).comp w
    (((thetaGauge_contDiffAt F) hP U V i w hw.1).div_const (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀))).add
      contDiffAt_const

theorem thetaLocalLog_exp (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w₀ w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (h₀ : w₀ ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i)
    (hw : w ∈ (thetaLogDomain F) hP U V i w₀) :
    Complex.exp ((thetaLocalLog F) hP U V i w₀ w) = RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w := by
  have hq := RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 w₀ h₀.1 h₀.2
  have hs : RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀ ∈ Complex.slitPlane :=
    (interior_subset : interior {x | RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 x /
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w₀ ∈ Complex.slitPlane} ⊆ _) hw.2
  unfold thetaLocalLog
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero hs),
    Complex.exp_log hq, div_mul_cancel₀ _ hq]

theorem thetaFrameConnection_local_log
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w₀ w v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (h₀ : w₀ ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) (hw : w ∈ (thetaLogDomain F) hP U V i w₀) :
    (Connection.Geometric.thetaFrameConnection F) hP U V i w v = RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm w v +
      fderiv ℂ ((thetaLocalLog F) hP U V i w₀) w v := by
  let f := (thetaLocalLog F) hP U V i w₀
  have hdiff : DifferentiableAt ℂ f w :=
    ((thetaLocalLog_contDiffAt F) hP U V i w₀ w hw).differentiableAt (by simp)
  have he : (fun x => Complex.exp (f x)) =ᶠ[𝓝 w] RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 := by
    filter_upwards [((thetaLogDomain_isOpen F) hP U V i w₀).mem_nhds hw] with x hx
    exact (thetaLocalLog_exp F) hP U V i w₀ x h₀ hx
  have hD : fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w v =
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w * fderiv ℂ f w v := by
    calc
      _ = fderiv ℂ (fun x => Complex.exp (f x)) w v :=
        congrArg (fun d : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →L[ℂ] ℂ => d v) he.fderiv_eq.symm
      _ = Complex.exp (f w) * fderiv ℂ f w v :=
        congrArg (fun d : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →L[ℂ] ℂ => d v) hdiff.hasFDerivAt.cexp.fderiv
      _ = _ := congrArg (fun c : ℂ => c * fderiv ℂ f w v) ((thetaLocalLog_exp F) hP U V i w₀ w h₀ hw)
  have hq := RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero U V i.1 i.2 w hw.1.1 hw.1.2
  unfold Connection.Geometric.thetaFrameConnection
  rw [hD, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalLog.Geometric
