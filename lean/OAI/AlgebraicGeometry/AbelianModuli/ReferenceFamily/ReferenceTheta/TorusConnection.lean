import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.FrameCurvature

/-! # Torus Connection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The original theta frame domains descend to genuine open subsets
of the period torus, with exact membership and connection invariance. -/

open _root_.TopologicalSpace

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaGaugeOpen_quotient_eq
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (v w : F.periodData.space)
    (h : (QuotientAddGroup.mk v : F.periodData.periodTorus) = QuotientAddGroup.mk w) :
    v ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i ↔ w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i := by
  have hl : v - w ∈ F.periodData.periodIntegerLattice.toAddSubgroup :=
    (@QuotientAddGroup.eq_iff_sub_mem F.periodData.space inferInstance
      F.periodData.periodIntegerLattice.toAddSubgroup inferInstance v w).mp h
  let l : F.periodData.periodIntegerLattice := ⟨v - w, hl⟩
  have hs : w + l.val = v := by dsimp only [l]; abel
  exact (congrArg (fun x => x ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) hs).symm.trans
    (propext (RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_translates U V i l w)) |>.to_iff

def Reference.Fiber.ReferenceAnalyticFiber.thetaTorusFrameOpen (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Opens F.periodData.periodTorus :=
  ⟨(QuotientAddGroup.mk : F.periodData.space → F.periodData.periodTorus) '' RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i,
    QuotientAddGroup.isOpenMap_coe _ (RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_isOpen U V i)⟩

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusFrameOpen_mk
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : F.periodData.space) :
    (QuotientAddGroup.mk w : F.periodData.periodTorus) ∈ F.thetaTorusFrameOpen hP U V i ↔
      w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i := by
  constructor
  · rintro ⟨v, hv, he⟩
    exact (F.thetaGaugeOpen_quotient_eq hP U V i v w he).mp hv
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusFrameOpen_cover (q : F.periodData.periodTorus) :
    ∃ i, q ∈ F.thetaTorusFrameOpen hP U V i := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨i, hi⟩ := RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen_cover U V w
  exact ⟨i, (F.thetaTorusFrameOpen_mk hP U V i w).mpr hi⟩

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusFrameOpen_chart
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k q : F.periodData.periodTorus)
    (hq : q ∈ (F.periodData.periodChart k).source) :
    F.periodData.periodChart k q ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i ↔ q ∈ F.thetaTorusFrameOpen hP U V i := by
  have h := (F.periodData.periodChart k).left_inv hq
  rw [F.periodData.periodChart_symm] at h
  exact (F.thetaTorusFrameOpen_mk hP U V i (F.periodData.periodChart k q)).symm.trans
    ((congrArg (fun t => t ∈ F.thetaTorusFrameOpen hP U V i) h).to_iff)

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnectionRaw_quotient_eq (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (v w : F.periodData.space)
    (h : (QuotientAddGroup.mk v : F.periodData.periodTorus) = QuotientAddGroup.mk w)
    (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) :
    F.thetaFrameConnectionRaw hP U V i v = F.thetaFrameConnectionRaw hP U V i w := by
  have hl : v - w ∈ F.periodData.periodIntegerLattice.toAddSubgroup :=
    (@QuotientAddGroup.eq_iff_sub_mem F.periodData.space inferInstance
      F.periodData.periodIntegerLattice.toAddSubgroup inferInstance v w).mp h
  let l : F.periodData.periodIntegerLattice := ⟨v - w, hl⟩
  have hs : w + l.val = v := by dsimp only [l]; abel
  ext a
  exact (congrArg (fun t => F.thetaFrameConnection hP U V i t (a 0)) hs).symm.trans
    (F.thetaFrameConnection_translates hP U V hdeg i l w (a 0) hw)

end

/-! The actual periodic theta-frame connection descends to a smooth
local one-form on the period torus in its genuine tangent bundle. -/

open _root_.TopologicalSpace Filter _root_.Topology
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaFrameConnectionRaw_contDiffAt
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (w : F.periodData.space)
    (hw : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i) : ContDiffAt ℝ ∞ (F.thetaFrameConnectionRaw hP U V i) w := by
  have hlog := F.thetaLogZeroForm_contDiffAt hP U V i w w (F.mem_thetaLogDomain hP U V i w hw)
  exact ((RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationConnectionForm F.form).smooth.contDiffAt.add
    (Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth.contDiffAt_extDeriv_of_add_one_le hlog (by simp))).congr_of_eventuallyEq
      (F.thetaFrameConnectionRaw_local hP U V i w hw)

def Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnectionCoefficients
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) : Analysis.DifferentialForms.Manifold.Basic.RawForm F.periodData.space 1 :=
  F.thetaFrameConnectionRaw hP U V i

def Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnectionRaw (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F.periodData.space F.periodData.periodTorus 1 := fun q =>
  Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (F.periodData.periodChart q) (F.thetaTorusConnectionCoefficients hP U V i) q

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnectionRaw_eq_chart (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k q : F.periodData.periodTorus)
    (hq : q ∈ (F.periodData.periodChart k).source) (hi : q ∈ F.thetaTorusFrameOpen hP U V i) :
    F.thetaTorusConnectionRaw hP U V i q =
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (F.periodData.periodChart k) (F.thetaTorusConnectionCoefficients hP U V i) q := by
  have h₁ := (F.periodData.periodChart q).left_inv (F.periodData.mem_periodChart_source q)
  have h₂ := (F.periodData.periodChart k).left_inv hq
  rw [F.periodData.periodChart_symm] at h₁ h₂
  have hc : F.thetaTorusConnectionCoefficients hP U V i (F.periodData.periodChart q q) =
      F.thetaTorusConnectionCoefficients hP U V i (F.periodData.periodChart k q) :=
    F.thetaFrameConnectionRaw_quotient_eq hP U V hdeg i
    (F.periodData.periodChart q q) (F.periodData.periodChart k q) (h₁.trans h₂.symm)
    ((F.thetaTorusFrameOpen_chart hP U V i k q hq).mpr hi)
  change (F.thetaTorusConnectionCoefficients hP U V i (F.periodData.periodChart q q)).compContinuousLinearMap _ = _
  rw [hc, F.periodData.periodChart_tangentMap_eq q k q (F.periodData.mem_periodChart_source q) hq]
  rfl

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnectionRaw_inChart (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : F.periodData.periodTorus)
    (w : F.periodData.space) (hw : w ∈ (F.periodData.periodChart k).target)
    (hi : (F.periodData.periodChart k).symm w ∈ F.thetaTorusFrameOpen hP U V i) :
    (F.thetaTorusConnectionRaw hP U V i).inChart (F.periodData.periodChart k) w =
      F.thetaTorusConnectionCoefficients hP U V i w := by
  calc
    _ = (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart (F.periodData.periodChart k)
        (F.thetaTorusConnectionCoefficients hP U V i)).inChart (F.periodData.periodChart k) w := by
      unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
      rw [F.thetaTorusConnectionRaw_eq_chart hP U V hdeg i k _
        ((F.periodData.periodChart k).map_target hw) hi]
    _ = _ := Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_fromChart_apply (F.periodData.periodChart k)
      (F.periodData.periodChart_mem_atlas k) (F.thetaTorusConnectionCoefficients hP U V i) hw

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnectionRaw_smooth (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (F.thetaTorusConnectionRaw hP U V i) (F.thetaTorusFrameOpen hP U V i) := by
  intro e he
  obtain ⟨k, rfl⟩ := he
  have hs : ContDiffOn ℝ ∞ (F.thetaTorusConnectionCoefficients hP U V i)
      (Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain (F.periodData.periodChart k) (F.thetaTorusFrameOpen hP U V i)) := by
    intro w hw
    have hi : (F.periodData.periodChart k).symm w ∈ F.thetaTorusFrameOpen hP U V i := hw.2
    rw [F.periodData.periodChart_symm] at hi
    exact (F.thetaFrameConnectionRaw_contDiffAt hP U V i w
      ((F.thetaTorusFrameOpen_mk hP U V i w).mp hi)).contDiffWithinAt
  apply hs.congr
  intro w hw
  exact F.thetaTorusConnectionRaw_inChart hP U V hdeg i k w hw.1 hw.2

def Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnection (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm F.periodData.space (F.thetaTorusFrameOpen hP U V i) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw _ (F.thetaTorusConnectionRaw hP U V i)
    (F.thetaTorusConnectionRaw_smooth hP U V hdeg i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
