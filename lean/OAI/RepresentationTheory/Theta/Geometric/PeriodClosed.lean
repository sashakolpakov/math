import OAI.RepresentationTheory.Theta.Geometric.Period.Derivative
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoEnergy

/-! # Period Closed -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The actual descended theta form is closed by the projective
positive-energy identity. It gives a canonical linear family of closed
forms and pure Betti classes before algebraic Albanese lifting. -/

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

theorem Data.ActiveHeckeThetaData.periodThetaSmoothForm_closed (φ : D.sphericalInputs) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (D.periodThetaSmoothForm X cover hcover hh ha φ) = 0 :=
  AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoEnergy.Closedness.projective_type10_with_type20_derivative_closed X
    (D.periodThetaSmoothForm X cover hcover hh ha φ)
    (D.periodThetaSmoothForm_bidegree X cover hcover hh ha φ)
    (D.periodThetaSmoothForm_derivative_pure X cover hcover hh ha φ)

def Data.ActiveHeckeThetaData.periodThetaSmoothLinear :
    D.sphericalInputs →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace 1 where
  toFun := D.periodThetaSmoothForm X cover hcover hh ha
  map_add' φ ψ := by
    apply Subtype.ext
    funext y
    ext v
    exact congrArg (fun c : X.analyticSpace → X.analyticModel →L[ℂ] ℂ => c y (v 0))
      ((D.periodThetaCovectorLinear X cover hcover).map_add φ ψ)
  map_smul' a φ := by
    apply Subtype.ext
    funext y
    ext v
    exact congrArg (fun c : X.analyticSpace → X.analyticModel →L[ℂ] ℂ => c y (v 0))
      ((D.periodThetaCovectorLinear X cover hcover).map_smul a φ)

def Data.ActiveHeckeThetaData.periodThetaClosedLinear :
    D.sphericalInputs →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 1 :=
  (D.periodThetaSmoothLinear X cover hcover hh ha).codRestrict _
    (D.periodThetaSmoothForm_closed X cover hcover hh ha)

def Data.ActiveHeckeThetaData.periodThetaBettiLinear : D.sphericalInputs →ₗ[ℂ] X.complexCohomology 1 where
  toFun φ := (X.deRhamBettiIso 1).hom
    (X.deRhamClass 1 (D.periodThetaClosedLinear X cover hcover hh ha φ))
  map_add' φ ψ := by simp only [map_add]
  map_smul' a φ := by simp only [map_smul, RingHom.id_apply]

theorem Data.ActiveHeckeThetaData.periodThetaBettiLinear_pure (φ : D.sphericalInputs) :
    D.periodThetaBettiLinear X cover hcover hh ha φ ∈ X.pureBettiSubspace 1 0 := by
  apply (X.mem_pureBettiSubspace_iff 1 0 _).mpr
  exact ⟨D.periodThetaClosedLinear X cover hcover hh ha φ,
    (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp
      (D.periodThetaSmoothForm_bidegree X cover hcover hh ha φ), rfl⟩

end

/-! The actual theta smooth form has exactly the original theta
covectors in the preferred ball chart. -/

open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.thetaBallSmoothForm_chart (hh : D.HasHolomorphicThetaData)
    (φ : D.sphericalInputs) (x : D.domain) (u : LinearTheta.BallCoordinates) :
    (D.thetaBallSmoothForm hh φ).val.inChart (chartAt LinearTheta.BallCoordinates x) x.val (fun _ => u) =
      D.thetaUniversal φ.val x.val u := by
  have h := Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_inChart
    (fun y : D.domain => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector LinearTheta.BallCoordinates (D.thetaUniversal φ.val y.val))
    (chartAt LinearTheta.BallCoordinates x) (chart_mem_atlas LinearTheta.BallCoordinates x) x.property
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue LinearTheta.BallCoordinates 1 => a (fun _ => u))
    (h.trans (Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply D.domain _ x))

end

end OAI.RepresentationTheory.Theta.Geometric
