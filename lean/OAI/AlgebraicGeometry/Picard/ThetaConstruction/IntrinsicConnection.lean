import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TorusCurvature
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ChernSmooth
import OAI.Analysis.DifferentialForms.Manifold.LocalPullback

/-! # Intrinsic Connection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Pull back the constructed torus connection to the actual native
algebraic frame domains. Its derivative is the native transported curvature. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaNativeFrame_period_domain
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (q : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) :
    M.period q ∈ AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i) ↔
      q ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact (M.thetaFrameOpen_period U V f g hf hg i w).trans ((TorusTheta.Geometric.thetaTorusFrameOpen_mk F) hP U V i w).symm

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaNativeFrame_period_inverse
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Set.MapsTo M.period.symm
      (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i))
      ((TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i) := by
  intro p hp
  apply (M.thetaNativeFrame_period_domain U V f g hf hg i (M.period.symm p)).mp
  exact (congrArg (fun x => x ∈ AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation
    (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i)) (M.period.apply_symm_apply p)).mpr hp

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeReferenceCurvature :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff)
    (PolarizationCurvature.Geometric.referenceTorusCurvature F)

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionRaw (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 1 :=
  ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).pullback M.period.symm

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionRaw_smooth (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (M.nativeThetaConnectionRaw U V i)
      (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i)) :=
  ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).pullback_smooth_on
    (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i)).isOpen
    ((TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i).isOpen ((TorusTheta.Geometric.thetaTorusConnectionRaw_smooth F) hP U V hdeg i)
    M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).contMDiffOn
    (M.thetaNativeFrame_period_inverse U V f g hf hg i)

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnection (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i)) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw _ (M.nativeThetaConnectionRaw U V i)
    (M.nativeThetaConnectionRaw_smooth U V f g hf hg hdeg i)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnection_curvature (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaConnection U V f g hf hg hdeg i) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen
        (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i))
        M.nativeReferenceCurvature := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  refine (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_ofRaw_apply (M.nativeThetaConnectionRaw U V i)
    (M.nativeThetaConnectionRaw_smooth U V f g hf hg hdeg i) p).trans ?_
  have hd := ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).exteriorDerivative_pullback_on
    (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left i)).isOpen
    ((TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i).isOpen ((TorusTheta.Geometric.thetaTorusConnectionRaw_smooth F) hP U V hdeg i)
    M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).contMDiffOn
    (M.thetaNativeFrame_period_inverse U V f g hf hg i) p.property
  refine hd.trans ?_
  have hc := (TorusCurvature.Geometric.thetaTorusConnectionRaw_derivative F) hP U V hdeg i (M.period.symm p.val)
    (M.thetaNativeFrame_period_inverse U V f g hf hg i p.property)
  exact congrArg (fun a : TangentSpace 𝓘(ℝ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (M.period.symm p.val) [⋀^Fin 2]→L[ℝ] ℂ =>
    a.compContinuousLinearMap (mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℝ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
      M.period.symm p.val)) hc

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
