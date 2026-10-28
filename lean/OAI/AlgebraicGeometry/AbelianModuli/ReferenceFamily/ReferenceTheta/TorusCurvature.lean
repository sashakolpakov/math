import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.TorusConnection

/-! # Torus Curvature -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Exterior differentiation of the descended theta-frame connection
is exactly the original global period-torus curvature. -/

open _root_.TopologicalSpace Filter _root_.Topology
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnectionRaw_derivative (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (q : F.periodData.periodTorus)
    (hq : q ∈ F.thetaTorusFrameOpen hP U V i) :
    (F.thetaTorusConnectionRaw hP U V i).exteriorDerivative q = F.referenceTorusCurvature q := by
  let e := F.periodData.periodChart q
  have he : q ∈ e.source := F.periodData.mem_periodChart_source q
  have hw : e q ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i := (F.thetaTorusFrameOpen_chart hP U V i q q he).mpr hq
  have hnear : (F.thetaTorusConnectionRaw hP U V i).inChart e =ᶠ[𝓝 (e q)]
      F.thetaTorusConnectionCoefficients hP U V i := by
    have ho := e.isOpen_inter_preimage_symm (F.thetaTorusFrameOpen hP U V i).isOpen
    have hm : e q ∈ e.target ∩ e.symm ⁻¹' (F.thetaTorusFrameOpen hP U V i) :=
      ⟨e.map_source he, (congrArg (fun t => t ∈ F.thetaTorusFrameOpen hP U V i) (e.left_inv he)).mpr hq⟩
    filter_upwards [ho.mem_nhds hm] with w hw
    exact F.thetaTorusConnectionRaw_inChart hP U V hdeg i q w hw.1 hw.2
  have hd : extDeriv (F.thetaTorusConnectionCoefficients hP U V i) (e q) =
      RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.form (e q) := F.thetaFrameConnectionRaw_curvature hP U V i (e q) hw
  change (extDeriv ((F.thetaTorusConnectionRaw hP U V i).inChart e) (e q)).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q) = _
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue F.periodData.space 2 => a.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q))
    (hnear.extDeriv_eq.trans hd)

theorem Reference.Fiber.ReferenceAnalyticFiber.thetaTorusConnection_curvature (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (F.thetaTorusConnection hP U V hdeg i) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (F.thetaTorusFrameOpen hP U V i) F.referenceTorusCurvature := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro q
  exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_ofRaw_apply (F.thetaTorusConnectionRaw hP U V i)
    (F.thetaTorusConnectionRaw_smooth hP U V hdeg i) q).trans
    (F.thetaTorusConnectionRaw_derivative hP U V hdeg i q.val q.property)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
