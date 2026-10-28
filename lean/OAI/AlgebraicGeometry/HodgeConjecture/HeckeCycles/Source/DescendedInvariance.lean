import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq

/-! # Descended Invariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DescendedInvariance.CM

noncomputable section

/-! The original descended one-form supplies its own principal-level
invariance. This is a derivative calculation on the actual ball cover,
independent of any splitting or automorphy compatibility hypothesis. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}

def ballMap (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : B.Domain → B.Domain :=
  fun z => ⟨UnitaryEq.CM.Frames.period E g z.val,
    RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_preserves B.b E.val.toRingHom g z.val z.property⟩

theorem ballMap_differentiable (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    MDifferentiable 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart) (ballMap E g) := by
  intro z
  have hf : DifferentiableAt ℂ (UnitaryEq.CM.Frames.period E g) z.val :=
    (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_differentiableOn B.b E.val.toRingHom g z.val z.property).differentiableAt
      (B.domain_isOpen.mem_nhds z.property)
  have h := hf.mdifferentiableAt.comp z
    ((contMDiff_subtype_val (I := 𝓘(ℂ, GeometricSource.CM.BallChart)) (n := ∞)).mdifferentiable (by simp) z)
  change MDifferentiableAt 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart)
    (Subtype.val ∘ ballMap E g) z at h
  simpa only [MDifferentiableAt, ChartedSpace.LiftPropAt,
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff] using h

theorem ballMap_derivative (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) :
    mfderiv 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart) (ballMap E g) z =
      fderiv ℂ (UnitaryEq.CM.Frames.period E g) z.val := by
  have hsub : MDifferentiableAt 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart)
      (Subtype.val : B.Domain → GeometricSource.CM.BallChart) z :=
    (contMDiff_subtype_val (I := 𝓘(ℂ, GeometricSource.CM.BallChart)) (n := ∞)).mdifferentiable (by simp) z
  have hf : DifferentiableAt ℂ (UnitaryEq.CM.Frames.period E g) z.val :=
    (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_differentiableOn B.b E.val.toRingHom g z.val z.property).differentiableAt
      (B.domain_isOpen.mem_nhds z.property)
  have hcod : (show GeometricSource.CM.BallChart →L[ℂ] GeometricSource.CM.BallChart from
      mfderiv 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart) (ballMap E g) z) =
      mfderiv 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart) (Subtype.val ∘ ballMap E g) z := by
    unfold mfderiv
    have he : MDifferentiableAt 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart)
        (Subtype.val ∘ ballMap E g) z ↔
        MDifferentiableAt 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart) (ballMap E g) z := by
      simp only [MDifferentiableAt, ChartedSpace.LiftPropAt,
        ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff]
    rw [he]
    rfl
  refine hcod.trans ?_
  change mfderiv 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart)
    ((UnitaryEq.CM.Frames.period E g) ∘ (Subtype.val : B.Domain → GeometricSource.CM.BallChart)) z = _
  erw [mfderiv_comp z hf.mdifferentiableAt hsub, mfderiv_eq_fderiv,
    show mfderiv 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, GeometricSource.CM.BallChart) (Subtype.val : B.Domain → GeometricSource.CM.BallChart) z =
      ContinuousLinearMap.id ℂ GeometricSource.CM.BallChart from mfderiv_extChartAt_self,
    ContinuousLinearMap.comp_id]

theorem period_eq_lineAction (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    UnitaryEq.CM.Frames.period E g z = GeometricSource.CM.BallDatum.lineAction (Matrix.SpecialLinearGroup.toLin' g.val) z := by
  rw [UnitaryEq.CM.Frames.period, RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_eq_fractional B.b E.val.toRingHom g z hz]
  funext i
  change RepresentationTheory.Theta.Geometric.Period.Ne.periodRow B.b E.val.toRingHom g i.castSucc z /
    RepresentationTheory.Theta.Geometric.Period.Ne.periodRow B.b E.val.toRingHom g 2 z = _
  rw [RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_eq_mulVec, RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_eq_mulVec]
  unfold GeometricSource.CM.BallDatum.lineAction
  rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.toMatrix'_toLin']
  rfl

theorem invariant (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : B.IsBallCover N X π)
    («ω» : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π «ω»)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (hg : B.principalLevel N (Matrix.SpecialLinearGroup.toLin' g.val))
    (z : B.Domain) (ξ : GeometricSource.CM.BallChart) :
    GeometricSource.CM.thetaOneForm E L φ (UnitaryEq.CM.Frames.period E g z.val) (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z.val ξ) =
      GeometricSource.CM.thetaOneForm E L φ z.val ξ := by
  have hp : π ∘ ballMap E g = π := by
    funext w
    exact ((hπ.2.2.2.2.2 w (ballMap E g w)).mpr
      ⟨Matrix.SpecialLinearGroup.toLin' g.val, hg, period_eq_lineAction E g w.val w.property⟩).symm
  have hd := mfderiv_comp (I := 𝓘(ℝ, GeometricSource.CM.BallChart)) (I' := 𝓘(ℝ, GeometricSource.CM.BallChart))
    (I'' := 𝓘(ℝ, X.analyticModel)) z
    (Theta.Matching.CM.mdifferentiableAt_real (hπ.2.2.2.1 (ballMap E g z)))
    (Theta.Matching.CM.mdifferentiableAt_real (ballMap_differentiable E g z))
  change (show GeometricSource.CM.BallChart →L[ℝ] X.analyticModel from
    mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) (π ∘ ballMap E g) z) =
      (show GeometricSource.CM.BallChart →L[ℝ] X.analyticModel from
        mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π (ballMap E g z)).comp
      (show GeometricSource.CM.BallChart →L[ℝ] GeometricSource.CM.BallChart from
        mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, GeometricSource.CM.BallChart) (ballMap E g) z) at hd
  erw [hp, Theta.Matching.CM.real_mfderiv_eq_complex (ballMap_differentiable E g z),
    ballMap_derivative E g z] at hd
  have hz : π (ballMap E g z) = π z := congrFun hp z
  change GeometricSource.CM.thetaOneForm E L φ (ballMap E g z).val
    (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z.val ξ) = GeometricSource.CM.thetaOneForm E L φ z.val ξ
  rw [← hω (ballMap E g z) (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z.val ξ), ← hω z ξ, hz]
  congr 1
  funext i
  exact (congrArg (fun A : GeometricSource.CM.BallChart →L[ℝ] X.analyticModel => A ξ) hd).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DescendedInvariance.CM
