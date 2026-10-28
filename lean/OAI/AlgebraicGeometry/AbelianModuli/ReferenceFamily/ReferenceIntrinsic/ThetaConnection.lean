import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.TorusCurvature
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.ChernSmooth
import OAI.Analysis.DifferentialForms.Manifold.LocalPullback

/-! # Theta Connection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Pull back the constructed torus connection to the actual native
algebraic frame domains. Its derivative is the native transported curvature. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaNativeFrame_period_domain
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (q : F.periodData.periodTorus) :
    M.period q ∈ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i) ↔
      q ∈ F.thetaTorusFrameOpen hP U V i := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact (M.thetaFrameOpen_period U V f g hf hg i w).trans (F.thetaTorusFrameOpen_mk hP U V i w).symm

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaNativeFrame_period_inverse
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Set.MapsTo M.period.symm
      (AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i))
      (F.thetaTorusFrameOpen hP U V i) := by
  intro p hp
  apply (M.thetaNativeFrame_period_domain U V f g hf hg i (M.period.symm p)).mp
  exact (congrArg (fun x => x ∈ AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation
    (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i)) (M.period.apply_symm_apply p)).mpr hp

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceCurvature :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff)
    F.referenceTorusCurvature

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionRaw (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 1 :=
  (F.thetaTorusConnectionRaw hP U V i).pullback M.period.symm

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionRaw_smooth (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (M.nativeThetaConnectionRaw U V i)
      (AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i)) :=
  (F.thetaTorusConnectionRaw hP U V i).pullback_smooth_on
    (AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i)).isOpen
    (F.thetaTorusFrameOpen hP U V i).isOpen (F.thetaTorusConnectionRaw_smooth hP U V hdeg i)
    M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).contMDiffOn
    (M.thetaNativeFrame_period_inverse U V f g hf hg i)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnection (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i)) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw _ (M.nativeThetaConnectionRaw U V i)
    (M.nativeThetaConnectionRaw_smooth U V f g hf hg hdeg i)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnection_curvature (hdeg : V.degree = U.degree + 1)
    (i : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaConnection U V f g hf hg hdeg i) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen
        (AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i))
        M.nativeReferenceCurvature := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  refine (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_ofRaw_apply (M.nativeThetaConnectionRaw U V i)
    (M.nativeThetaConnectionRaw_smooth U V f g hf hg hdeg i) p).trans ?_
  have hd := (F.thetaTorusConnectionRaw hP U V i).exteriorDerivative_pullback_on
    (AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left i)).isOpen
    (F.thetaTorusFrameOpen hP U V i).isOpen (F.thetaTorusConnectionRaw_smooth hP U V hdeg i)
    M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).contMDiffOn
    (M.thetaNativeFrame_period_inverse U V f g hf hg i) p.property
  refine hd.trans ?_
  have hc := F.thetaTorusConnectionRaw_derivative hP U V hdeg i (M.period.symm p.val)
    (M.thetaNativeFrame_period_inverse U V f g hf hg i p.property)
  exact congrArg (fun a : TangentSpace 𝓘(ℝ, F.periodData.space) (M.period.symm p.val) [⋀^Fin 2]→L[ℝ] ℂ =>
    a.compContinuousLinearMap (mfderiv 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℝ, F.periodData.space)
      M.period.symm p.val)) hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
