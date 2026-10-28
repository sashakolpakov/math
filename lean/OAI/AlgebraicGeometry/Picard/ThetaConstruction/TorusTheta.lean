import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalLog
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationCurvature
import OAI.Analysis.DifferentialForms.Manifold.DegreeZero

/-! # Torus Theta -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.TorusTheta.Geometric

noncomputable section

section

/-! The actual exterior derivative of the algebraic theta-frame
connection equals the original Gaussian curvature on every frame
domain. Local holomorphic logarithms provide the exact primitives. -/

open OAI.Analysis.DifferentialForms.Manifold.DegreeZero Set Filter _root_.Topology
open scoped ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))

def thetaFrameConnectionRaw (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Basic.RawForm (DefinitionsIntegral.Tangent dim) 1 := fun w =>
  let dq : DefinitionsIntegral.Tangent dim →L[ℝ] ℂ := (fderiv ℂ (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2) w).restrictScalars ℝ
  ContinuousAlternatingMap.ofSubsingleton ℝ (DefinitionsIntegral.Tangent dim) ℂ (0 : Fin 1)
    (RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm w + (RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w)⁻¹ • dq)

theorem thetaFrameConnectionRaw_apply
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : DefinitionsIntegral.Tangent dim)
    (v : Fin 1 → DefinitionsIntegral.Tangent dim) :
    (thetaFrameConnectionRaw F) hP U V i w v = (Connection.Geometric.thetaFrameConnection F) hP U V i w (v 0) := rfl

def thetaLogZeroForm (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (w₀ : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) : Analysis.DifferentialForms.Manifold.Basic.RawForm (DefinitionsIntegral.Tangent dim) 0 := fun w =>
  ContinuousAlternatingMap.constOfIsEmpty ℝ (DefinitionsIntegral.Tangent dim) (Fin 0) ((LocalLog.Geometric.thetaLocalLog F) hP U V i w₀ w)

theorem thetaLogZeroForm_contDiffAt
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w₀ w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hw : w ∈ (LocalLog.Geometric.thetaLogDomain F) hP U V i w₀) :
    ContDiffAt ℝ ∞ ((thetaLogZeroForm F) hP U V i w₀) w := by
  have h : ContDiffAt ℝ ∞ ((LocalLog.Geometric.thetaLocalLog F) hP U V i w₀) w :=
    ((LocalLog.Geometric.thetaLocalLog_contDiffAt F) hP U V i w₀ w hw).restrict_scalars ℝ
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (DefinitionsIntegral.Tangent dim) ℂ (Fin 0)).contDiff.contDiffAt.comp w h

theorem thetaFrameConnectionRaw_local
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w₀ : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (h₀ : w₀ ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    (thetaFrameConnectionRaw F) hP U V i =ᶠ[𝓝 w₀]
      (fun w => RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.riemannForm w + extDeriv ((thetaLogZeroForm F) hP U V i w₀) w) := by
  have hm := (LocalLog.Geometric.mem_thetaLogDomain F) hP U V i w₀ h₀
  filter_upwards [((LocalLog.Geometric.thetaLogDomain_isOpen F) hP U V i w₀).mem_nhds hm] with w hw
  ext v
  refine ((thetaFrameConnectionRaw_apply F) hP U V i w v).trans ?_
  have hreal := (((LocalLog.Geometric.thetaLocalLog_contDiffAt F) hP U V i w₀ w hw).differentiableAt (by simp)).fderiv_restrictScalars ℝ
  have hd : extDeriv ((thetaLogZeroForm F) hP U V i w₀) w v =
      fderiv ℂ ((LocalLog.Geometric.thetaLocalLog F) hP U V i w₀) w (v 0) := by
    exact (congrArg (fun t : Analysis.DifferentialForms.Manifold.Basic.FormValue (DefinitionsIntegral.Tangent dim) 1 => t v)
      (extDeriv_constOfIsEmpty (𝕜 := ℝ)
        (fun x : DefinitionsIntegral.Tangent dim => (LocalLog.Geometric.thetaLocalLog F) hP U V i w₀ x) w)).trans
      (congrArg (fun d : (ProjectivePeriodData.Geometric.projectivePeriodData F).space →L[ℝ] ℂ => d (v 0)) hreal)
  exact ((LocalLog.Geometric.thetaFrameConnection_local_log F) hP U V i w₀ w (v 0) h₀ hw).trans
    (congrArg (fun c : ℂ => RepresentationTheory.Theta.Geometric.PolarizationConnection.polarizationConnection F.riemannForm w (v 0) + c) hd.symm)

theorem thetaFrameConnectionRaw_curvature
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    extDeriv ((thetaFrameConnectionRaw F) hP U V i) w = (PolarizationCurvature.Geometric.referenceCurvature F) w := by
  have hlog := (thetaLogZeroForm_contDiffAt F) hP U V i w w ((LocalLog.Geometric.mem_thetaLogDomain F) hP U V i w hw)
  have hdlog : ContDiffAt ℝ ∞ (extDeriv ((thetaLogZeroForm F) hP U V i w)) w :=
    Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffAt_extDeriv_of_add_one_le hlog (by simp)
  refine ((thetaFrameConnectionRaw_local F) hP U V i w hw).extDeriv_eq.trans ?_
  have hsum := extDeriv_fun_add
    ((RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.riemannForm).smooth.differentiable (by simp) w)
    (hdlog.differentiableAt (by simp))
  exact hsum.trans ((congrArg
    (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue (DefinitionsIntegral.Tangent dim) 2 => extDeriv (RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.riemannForm) w + a)
    (Analysis.DifferentialForms.Manifold.SquareZero.extDeriv_extDeriv_of_contDiffAt hlog)).trans (add_zero _))

end

section

/-! The original theta frame domains descend to genuine open subsets
of the period torus, with exact membership and connection invariance. -/

open OAI.Analysis.DifferentialForms.Manifold.DegreeZero _root_.TopologicalSpace

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))

theorem thetaGaugeOpen_quotient_eq
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (v w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (h : (QuotientAddGroup.mk v : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) = QuotientAddGroup.mk w) :
    v ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i ↔ w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i := by
  have hl : v - w ∈ (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice.toAddSubgroup :=
    (@QuotientAddGroup.eq_iff_sub_mem (ProjectivePeriodData.Geometric.projectivePeriodData F).space inferInstance
      (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice.toAddSubgroup inferInstance v w).mp h
  let l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice := ⟨v - w, hl⟩
  have hs : w + l.val = v := by dsimp only [l]; abel
  exact (congrArg (fun x => x ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) hs).symm.trans
    (propext (RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_translates U V i l w)) |>.to_iff

def thetaTorusFrameOpen (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Opens (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus :=
  ⟨(QuotientAddGroup.mk : (ProjectivePeriodData.Geometric.projectivePeriodData F).space → (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) '' RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i,
    QuotientAddGroup.isOpenMap_coe _ (RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_isOpen U V i)⟩

theorem thetaTorusFrameOpen_mk
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    (QuotientAddGroup.mk w : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) ∈ (thetaTorusFrameOpen F) hP U V i ↔
      w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i := by
  constructor
  · rintro ⟨v, hv, he⟩
    exact ((thetaGaugeOpen_quotient_eq F) hP U V i v w he).mp hv
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem thetaTorusFrameOpen_cover (q : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) :
    ∃ i, q ∈ (thetaTorusFrameOpen F) hP U V i := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨i, hi⟩ := RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_cover U V w
  exact ⟨i, ((thetaTorusFrameOpen_mk F) hP U V i w).mpr hi⟩

theorem thetaTorusFrameOpen_chart
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k q : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
    (hq : q ∈ ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).source) :
    (ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k q ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i ↔ q ∈ (thetaTorusFrameOpen F) hP U V i := by
  have h := ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).left_inv hq
  rw [(ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart_symm] at h
  exact ((thetaTorusFrameOpen_mk F) hP U V i ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k q)).symm.trans
    ((congrArg (fun t => t ∈ (thetaTorusFrameOpen F) hP U V i) h).to_iff)

theorem thetaFrameConnectionRaw_quotient_eq (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (v w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (h : (QuotientAddGroup.mk v : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) = QuotientAddGroup.mk w)
    (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    (thetaFrameConnectionRaw F) hP U V i v = (thetaFrameConnectionRaw F) hP U V i w := by
  have hl : v - w ∈ (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice.toAddSubgroup :=
    (@QuotientAddGroup.eq_iff_sub_mem (ProjectivePeriodData.Geometric.projectivePeriodData F).space inferInstance
      (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice.toAddSubgroup inferInstance v w).mp h
  let l : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodIntegerLattice := ⟨v - w, hl⟩
  have hs : w + l.val = v := by dsimp only [l]; abel
  ext a
  exact (congrArg (fun t => (Connection.Geometric.thetaFrameConnection F) hP U V i t (a 0)) hs).symm.trans
    ((Connection.Geometric.thetaFrameConnection_translates F) hP U V hdeg i l w (a 0) hw)

end

/-! The actual periodic theta-frame connection descends to a smooth
local one-form on the period torus in its genuine tangent bundle. -/

open OAI.Analysis.DifferentialForms.Manifold.DegreeZero _root_.TopologicalSpace Filter _root_.Topology
open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))

theorem thetaFrameConnectionRaw_contDiffAt
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) : ContDiffAt ℝ ∞ ((thetaFrameConnectionRaw F) hP U V i) w := by
  have hlog := (thetaLogZeroForm_contDiffAt F) hP U V i w w ((LocalLog.Geometric.mem_thetaLogDomain F) hP U V i w hw)
  exact ((RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.riemannForm).smooth.contDiffAt.add
    (Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffAt_extDeriv_of_add_one_le hlog (by simp))).congr_of_eventuallyEq
      ((thetaFrameConnectionRaw_local F) hP U V i w hw)

def thetaTorusConnectionCoefficients
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) : Analysis.DifferentialForms.Manifold.Basic.RawForm (ProjectivePeriodData.Geometric.projectivePeriodData F).space 1 :=
  (thetaFrameConnectionRaw F) hP U V i

def thetaTorusConnectionRaw (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (ProjectivePeriodData.Geometric.projectivePeriodData F).space (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus 1 := fun q =>
  Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q) ((thetaTorusConnectionCoefficients F) hP U V i) q

theorem thetaTorusConnectionRaw_eq_chart (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k q : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
    (hq : q ∈ ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).source) (hi : q ∈ (thetaTorusFrameOpen F) hP U V i) :
    (thetaTorusConnectionRaw F) hP U V i q =
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k) ((thetaTorusConnectionCoefficients F) hP U V i) q := by
  have h₁ := ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q).left_inv ((ProjectivePeriodData.Geometric.projectivePeriodData F).mem_periodChart_source q)
  have h₂ := ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).left_inv hq
  rw [(ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart_symm] at h₁ h₂
  have hc : (thetaTorusConnectionCoefficients F) hP U V i ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q q) =
      (thetaTorusConnectionCoefficients F) hP U V i ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k q) :=
    (thetaFrameConnectionRaw_quotient_eq F) hP U V hdeg i
    ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q q) ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k q) (h₁.trans h₂.symm)
    (((thetaTorusFrameOpen_chart F) hP U V i k q hq).mpr hi)
  change ((thetaTorusConnectionCoefficients F) hP U V i ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q q)).compContinuousLinearMap _ = _
  rw [hc, (ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart_tangentMap_eq q k q ((ProjectivePeriodData.Geometric.projectivePeriodData F).mem_periodChart_source q) hq]
  rfl

theorem thetaTorusConnectionRaw_inChart (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
    (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (hw : w ∈ ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).target)
    (hi : ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).symm w ∈ (thetaTorusFrameOpen F) hP U V i) :
    ((thetaTorusConnectionRaw F) hP U V i).inChart ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k) w =
      (thetaTorusConnectionCoefficients F) hP U V i w := by
  calc
    _ = (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k)
        ((thetaTorusConnectionCoefficients F) hP U V i)).inChart ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k) w := by
      unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
      rw [(thetaTorusConnectionRaw_eq_chart F) hP U V hdeg i k _
        (((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).map_target hw) hi]
    _ = _ := Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_fromChart_apply ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k)
      ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart_mem_atlas k) ((thetaTorusConnectionCoefficients F) hP U V i) hw

theorem thetaTorusConnectionRaw_smooth (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn ((thetaTorusConnectionRaw F) hP U V i) ((thetaTorusFrameOpen F) hP U V i) := by
  intro e he
  obtain ⟨k, rfl⟩ := he
  have hs : ContDiffOn ℝ ∞ ((thetaTorusConnectionCoefficients F) hP U V i)
      (Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k) ((thetaTorusFrameOpen F) hP U V i)) := by
    intro w hw
    have hi : ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k).symm w ∈ (thetaTorusFrameOpen F) hP U V i := hw.2
    rw [(ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart_symm] at hi
    exact ((thetaFrameConnectionRaw_contDiffAt F) hP U V i w
      (((thetaTorusFrameOpen_mk F) hP U V i w).mp hi)).contDiffWithinAt
  apply hs.congr
  intro w hw
  exact (thetaTorusConnectionRaw_inChart F) hP U V hdeg i k w hw.1 hw.2

def thetaTorusConnection (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (ProjectivePeriodData.Geometric.projectivePeriodData F).space ((thetaTorusFrameOpen F) hP U V i) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw _ ((thetaTorusConnectionRaw F) hP U V i)
    ((thetaTorusConnectionRaw_smooth F) hP U V hdeg i)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.TorusTheta.Geometric
