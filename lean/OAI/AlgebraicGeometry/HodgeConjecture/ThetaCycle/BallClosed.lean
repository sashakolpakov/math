import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallForms
import OAI.Analysis.HodgeTheory.Pure

/-! # Ball Closed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallClosed.CM

noncomputable section

/-! ThetaCycle: closedness of the constructed holomorphic top forms on the ball. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing

def coordinateHolomorphicTwo : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2 :=
  AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge
    (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector HeckeCycles.GeometricSource.CM.BallChart (ContinuousLinearMap.proj (0 : Fin 2)))
    (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector HeckeCycles.GeometricSource.CM.BallChart (ContinuousLinearMap.proj (1 : Fin 2)))

theorem coordinate_holomorphic_two_apply (v : Fin 2 → HeckeCycles.GeometricSource.CM.BallChart) :
    coordinateHolomorphicTwo v = v 0 0 * v 1 1 - v 1 0 * v 0 1 := by
  rw [coordinateHolomorphicTwo, ComplexMultiplication.HodgeComparison.Powers.CM.Construction.covectorWedge_one_one]
  rfl

theorem coordinate_holomorphic_two_pure : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree HeckeCycles.GeometricSource.CM.BallChart 2 0 coordinateHolomorphicTwo :=
  AlgebraicTopology.Kunneth.CovectorWedge.Constructions.hasBidegree_covectorWedge _ _ (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree HeckeCycles.GeometricSource.CM.BallChart _)
    (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree HeckeCycles.GeometricSource.CM.BallChart _)

theorem coordinate_holomorphic_two_basis :
    coordinateHolomorphicTwo (Pi.basisFun ℂ (Fin 2)) = 1 := by
  simp [coordinate_holomorphic_two_apply]

theorem complex_covector_two_expansion (f : HeckeCycles.GeometricSource.CM.BallChart →L[ℂ] ℂ) (v : HeckeCycles.GeometricSource.CM.BallChart) :
    f v = v 0 * f (Pi.single 0 1) + v 1 * f (Pi.single 1 1) := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  calc
    f v = f (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1) := congrArg f hv
    _ = _ := by simp

/-- Holomorphic multiples of `dz₁ ∧ dz₂` are closed for the actual real exterior derivative. -/
theorem holomorphic_two_extDeriv_zero {f : HeckeCycles.GeometricSource.CM.BallChart → ℂ} {z : HeckeCycles.GeometricSource.CM.BallChart}
    (hf : DifferentiableAt ℂ f z) :
    extDeriv (fun y => f y • coordinateHolomorphicTwo) z = 0 := by
  have hd (w : Fin 2 → HeckeCycles.GeometricSource.CM.BallChart) (u : HeckeCycles.GeometricSource.CM.BallChart) :
      fderiv ℝ (fun y => (f y • coordinateHolomorphicTwo) w) z u =
        fderiv ℂ f z u * coordinateHolomorphicTwo w := by
    have h := congrArg (fun L : HeckeCycles.GeometricSource.CM.BallChart →L[ℝ] ℂ => L u)
      ((hf.hasFDerivAt.mul_const (coordinateHolomorphicTwo w)).restrictScalars ℝ).fderiv
    change fderiv ℝ (fun y => (f y • coordinateHolomorphicTwo) w) z u =
      coordinateHolomorphicTwo w * fderiv ℂ f z u at h
    exact h.trans (mul_comm _ _)
  ext v
  rw [extDeriv_apply ((hf.restrictScalars ℝ).smul_const coordinateHolomorphicTwo)]
  simp_rw [hd]
  simp only [Fin.sum_univ_succ, coordinate_holomorphic_two_apply, Fin.removeNth]
  simp
  rw [complex_covector_two_expansion _ (v 0), complex_covector_two_expansion _ (v 1),
    complex_covector_two_expansion _ (v 2)]
  rw [show (2 : Fin 3).succAbove (1 : Fin 2) = 1 from rfl]
  ring

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d₀ d₁ : Gal(K/ℚ) → Bool}

theorem source_wedge_holomorphic
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    DifferentiableOn ℂ (Slots.CM.sourceWedgeCoefficient K L₀ L₁ φ ψ) B.domain := by
  have h₀ := Projection.CM.source_theta_covector_holomorphic K L₀ φ
  have h₁ := Projection.CM.source_theta_covector_holomorphic K L₁ ψ
  have he₀ (v : HeckeCycles.GeometricSource.CM.BallChart) := h₀.clm_apply (differentiableOn_const v)
  have he₁ (v : HeckeCycles.GeometricSource.CM.BallChart) := h₁.clm_apply (differentiableOn_const v)
  unfold Slots.CM.sourceWedgeCoefficient RepresentationTheory.Theta.Kernel.Calculus.wedgeCoefficient Slots.CM.sourceThetaCoordinates
  simp only [SparseSpanning.CM.jacobiCoefficients, LinearMap.coe_mk, AddHom.coe_mk]
  exact ((he₀ _).mul (he₁ _)).sub ((he₀ _).mul (he₁ _))

theorem source_ball_two_inChart
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places))
    (e : OpenPartialHomeomorph B.Domain HeckeCycles.GeometricSource.CM.BallChart) (he : e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain)
    {z : HeckeCycles.GeometricSource.CM.BallChart} (hz : z ∈ B.domain) :
    (BallForms.CM.sourceBallTwoForm K L₀ L₁ φ ψ).val.inChart e z =
      Slots.CM.sourceWedgeCoefficient K L₀ L₁ φ ψ z • coordinateHolomorphicTwo := by
  have hzt : z ∈ e.target := by rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he]
  ext v
  rw [Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing.pure_eq_basis_det _ (BallForms.CM.source_ball_two_pure K L₀ L₁ φ ψ e he z hzt)
    (Pi.basisFun ℂ (Fin 2)), BallForms.CM.source_ball_two_coefficient K L₀ L₁ φ ψ e he hz,
    ContinuousAlternatingMap.smul_apply,
    Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing.pure_eq_basis_det _ coordinate_holomorphic_two_pure (Pi.basisFun ℂ (Fin 2)),
    coordinate_holomorphic_two_basis, one_mul]
  rfl

theorem source_ball_two_closed
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (BallForms.CM.sourceBallTwoForm K L₀ L₁ φ ψ) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro z
  let e := chartAt HeckeCycles.GeometricSource.CM.BallChart z
  have he : e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain := chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart z
  have hzs : z ∈ e.source := mem_chart_source HeckeCycles.GeometricSource.CM.BallChart z
  have hzt : (z : HeckeCycles.GeometricSource.CM.BallChart) ∈ e.target := by
    rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he]
    exact z.property
  have hlocal : (BallForms.CM.sourceBallTwoForm K L₀ L₁ φ ψ).val.inChart e =ᶠ[𝓝 (z : HeckeCycles.GeometricSource.CM.BallChart)]
      (fun y => Slots.CM.sourceWedgeCoefficient K L₀ L₁ φ ψ y • coordinateHolomorphicTwo) := by
    filter_upwards [B.domain_isOpen.mem_nhds z.property] with y hy
    exact source_ball_two_inChart K L₀ L₁ φ ψ e he hy
  have hz : (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (BallForms.CM.sourceBallTwoForm K L₀ L₁ φ ψ)).val.inChart e z = 0 := by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hzt, hlocal.extDeriv_eq]
    exact holomorphic_two_extDeriv_zero
      ((source_wedge_holomorphic K L₀ L₁ φ ψ z z.property).differentiableAt
        (B.domain_isOpen.mem_nhds z.property))
  ext v
  have hv := congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 3 =>
    f (fun i => Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he z hzs (v i))) hz
  change (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (BallForms.CM.sourceBallTwoForm K L₀ L₁ φ ψ)).val.inChart e (e z) _ = _ at hv
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ e he z hzs] at hv
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hv
  exact hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallClosed.CM
