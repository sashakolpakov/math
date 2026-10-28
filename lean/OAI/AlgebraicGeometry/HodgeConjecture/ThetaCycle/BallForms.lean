import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Slots
import OAI.Analysis.DifferentialForms.Manifold.OpenEquivalence
import OAI.AlgebraicTopology.Kunneth.ManifoldWedge
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers

/-! # Ball Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallForms.CM

noncomputable section

/-!
ThetaCycle: actual pure differential forms on the ball from the literal theta
coefficients. Their exterior product is the native manifold wedge, and its
nonzero value is identified with the constructed theta determinant.
-/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicTopology.Kunneth.ManifoldWedge.Constructions

/-- The usual conversion of a complex covector to a real alternating one-form. -/
def complexCovectorCLM (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] :
    (E →L[ℂ] ℂ) →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.restrictScalarsIsometry ℂ E ℂ ℝ ℝ).toContinuousLinearMap

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d d₀ d₁ : Gal(K/ℚ) → Bool}

def sourceOpenOneForm (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm B.domainOpen 1 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw B.domainOpen
    (fun z => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector HeckeCycles.GeometricSource.CM.BallChart (Projection.CM.sourceThetaCovector K L φ z))
    ((complexCovectorCLM HeckeCycles.GeometricSource.CM.BallChart).contDiff.comp_contDiffOn (Projection.CM.source_theta_covector_smooth K L φ))

/-- A genuine smooth one-form on the induced ball manifold. -/
def sourceBallOneForm (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 1 :=
  Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv B.domainOpen 1 (sourceOpenOneForm K L φ)

theorem source_ball_one_inChart (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places))
    (e : OpenPartialHomeomorph B.Domain HeckeCycles.GeometricSource.CM.BallChart) (he : e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain)
    {z : HeckeCycles.GeometricSource.CM.BallChart} (hz : z ∈ B.domain) :
    (sourceBallOneForm K L φ).val.inChart e z =
      Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector HeckeCycles.GeometricSource.CM.BallChart (Projection.CM.sourceThetaCovector K L φ z) := by
  change (Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv B.domainOpen 1 (sourceOpenOneForm K L φ)).inChart e z = _
  rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_inChart _ e he hz]
  exact Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply B.domainOpen _ ⟨z, hz⟩

theorem source_ball_one_pure (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 1 0 (sourceBallOneForm K L φ).val := by
  intro e he z hz
  have hzB : z ∈ B.domain := by rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he] at hz
  rw [source_ball_one_inChart K L φ e he hzB]
  exact Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree HeckeCycles.GeometricSource.CM.BallChart _

/-- The ordinary exterior product, on actual tangent spaces of the ball. -/
def sourceBallTwoForm (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 :=
  AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (sourceBallOneForm K L₀ φ) (sourceBallOneForm K L₁ ψ)

theorem source_ball_two_coefficient
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places))
    (e : OpenPartialHomeomorph B.Domain HeckeCycles.GeometricSource.CM.BallChart) (he : e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain)
    {z : HeckeCycles.GeometricSource.CM.BallChart} (hz : z ∈ B.domain) :
    (sourceBallTwoForm K L₀ L₁ φ ψ).val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
      Slots.CM.sourceWedgeCoefficient K L₀ L₁ φ ψ z := by
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (sourceBallOneForm K L₀ φ).val
    (sourceBallOneForm K L₁ ψ).val).inChart e z _ = _
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
  dsimp only
  rw [source_ball_one_inChart K L₀ φ e he hz,
    source_ball_one_inChart K L₁ ψ e he hz, ComplexMultiplication.HodgeComparison.Powers.CM.Construction.covectorWedge_one_one]
  rfl

theorem source_ball_two_pure
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 (sourceBallTwoForm K L₀ L₁ φ ψ).val :=
  AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.hasManifoldBidegree_wedge (source_ball_one_pure K L₀ φ) (source_ball_one_pure K L₁ ψ)

variable [IsGalois ℚ K]

/-- Nonvanishing is proved for the actual exterior product of theta forms. -/
theorem exists_source_ball_two_nonzero
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (z : B.Domain) :
    ∃ φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places), sourceBallTwoForm K L₀ L₁ φ ψ ≠ 0 := by
  obtain ⟨φ, ψ, hφψ⟩ := Slots.CM.exists_source_wedge_nonzero K L₀ L₁ z z.property
  refine ⟨φ, ψ, fun hzero => hφψ ?_⟩
  rw [← source_ball_two_coefficient K L₀ L₁ φ ψ (chartAt HeckeCycles.GeometricSource.CM.BallChart z)
    (chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart z) z.property, hzero]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallForms.CM
