import OAI.RepresentationTheory.Theta.Geometric.Period.ThetaAt
import OAI.RepresentationTheory.Theta.Geometric.Period.CoverLocalSections
import OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorForms
import OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorPurity
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

/-! # Smooth Theta -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original theta covectors descend to a genuine smooth (1,0)
form on any actual period quotient, with their exact pullback formula. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)

def Data.ActiveHeckeThetaData.thetaBallSmoothForm (φ : D.sphericalInputs) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm LinearTheta.BallCoordinates D.domain 1 :=
  Complex.CovectorForms.holomorphicCovectorManifoldForm D.domain (D.thetaUniversal φ.val)
    (LinearTheta.canonical_oneForm_holomorphic D.domain D.period hh.1 D.project hh.2 φ.val)

include hh ha

theorem Data.ActiveHeckeThetaData.periodThetaRaw_pullback (φ : D.sphericalInputs) :
    (Complex.CovectorPurity.complexCovectorRawForm (D.periodThetaCovector X cover hcover φ)).pullback
      (E := LinearTheta.BallCoordinates) cover = (D.thetaBallSmoothForm hh φ).val := by
  funext x
  ext v
  have hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable
    hcover.2.2.1
  change D.periodThetaCovector X cover hcover φ (cover x)
    (mfderiv 𝓘(ℝ, LinearTheta.BallCoordinates) 𝓘(ℝ, X.analyticModel) cover x (v 0)) = _
  rw [AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex ((hc.of_le (by simp)).contMDiffAt)]
  exact (D.periodThetaCovector_pullback X cover hcover ha φ x (v 0)).trans
    (Complex.CovectorForms.holomorphicCovectorManifoldForm_apply D.domain (D.thetaUniversal φ.val) _ x v).symm

theorem Data.ActiveHeckeThetaData.periodThetaRaw_smooth (φ : D.sphericalInputs) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (Complex.CovectorPurity.complexCovectorRawForm (D.periodThetaCovector X cover hcover φ)) Set.univ := by
  have hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable
    hcover.2.2.1
  apply SmoothFormLocalSections.smoothForm_of_localSections _ cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
  · rw [D.periodThetaRaw_pullback X cover hcover hh ha φ]
    exact (D.thetaBallSmoothForm hh φ).smooth
  · exact Period.CoverLocalSections.holomorphicCover_hasLocalSections cover hcover.1 hcover.2.1 hcover.2.2.1 hcover.2.2.2.1

def Data.ActiveHeckeThetaData.periodThetaSmoothForm (φ : D.sphericalInputs) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace 1 :=
  ⟨Complex.CovectorPurity.complexCovectorRawForm (D.periodThetaCovector X cover hcover φ),
    D.periodThetaRaw_smooth X cover hcover hh ha φ⟩

theorem Data.ActiveHeckeThetaData.periodThetaSmoothForm_bidegree (φ : D.sphericalInputs) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace 1 0
      (D.periodThetaSmoothForm X cover hcover hh ha φ).val :=
  Complex.CovectorPurity.complexCovectorRawForm_bidegree _

end

end OAI.RepresentationTheory.Theta.Geometric
