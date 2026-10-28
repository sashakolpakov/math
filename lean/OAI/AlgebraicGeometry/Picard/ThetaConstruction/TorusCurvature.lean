import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TorusTheta

/-! # Torus Curvature -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.TorusCurvature.Geometric

noncomputable section

/-! Exterior differentiation of the descended theta-frame connection
is exactly the original global period-torus curvature. -/

open _root_.TopologicalSpace Filter _root_.Topology
open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))

theorem thetaTorusConnectionRaw_derivative (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (q : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
    (hq : q ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i) :
    ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).exteriorDerivative q = (PolarizationCurvature.Geometric.referenceTorusCurvature F) q := by
  let e := (ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q
  have he : q ∈ e.source := (ProjectivePeriodData.Geometric.projectivePeriodData F).mem_periodChart_source q
  have hw : e q ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V i := ((TorusTheta.Geometric.thetaTorusFrameOpen_chart F) hP U V i q q he).mpr hq
  have hnear : ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).inChart e =ᶠ[𝓝 (e q)]
      (TorusTheta.Geometric.thetaTorusConnectionCoefficients F) hP U V i := by
    have ho := e.isOpen_inter_preimage_symm ((TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i).isOpen
    have hm : e q ∈ e.target ∩ e.symm ⁻¹' ((TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i) :=
      ⟨e.map_source he, (congrArg (fun t => t ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i) (e.left_inv he)).mpr hq⟩
    filter_upwards [ho.mem_nhds hm] with w hw
    exact (TorusTheta.Geometric.thetaTorusConnectionRaw_inChart F) hP U V hdeg i q w hw.1 hw.2
  have hd : extDeriv ((TorusTheta.Geometric.thetaTorusConnectionCoefficients F) hP U V i) (e q) =
      RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.riemannForm (e q) := (TorusTheta.Geometric.thetaFrameConnectionRaw_curvature F) hP U V i (e q) hw
  change (extDeriv (((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).inChart e) (e q)).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q) = _
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ProjectivePeriodData.Geometric.projectivePeriodData F).space 2 => a.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e q))
    (hnear.extDeriv_eq.trans hd)

theorem thetaTorusConnection_curvature (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d ((TorusTheta.Geometric.thetaTorusConnection F) hP U V hdeg i) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ((TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i) (PolarizationCurvature.Geometric.referenceTorusCurvature F) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro q
  exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_ofRaw_apply ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i)
    ((TorusTheta.Geometric.thetaTorusConnectionRaw_smooth F) hP U V hdeg i) q).trans
    ((thetaTorusConnectionRaw_derivative F) hP U V hdeg i q.val q.property)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.TorusCurvature.Geometric
