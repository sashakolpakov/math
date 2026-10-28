import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicSourceTotalFactorization
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PureTopCoefficient
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalBallForms

/-! # Ball Wedge Decomposition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallWedgeDecomposition.CM

noncomputable section

/-! Equality of genuine pure top forms follows from their actual chart
coefficients. Apply the full native ThetaKernel source factorization to obtain
finite sums of genuine wedges on the original ball. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K}

theorem pure_ball_top_eq_of_coefficients
    (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 α.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 β.val)
    (hcoeff : ∀ (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart B.Domain) z, z ∈ B.domain →
      α.val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) =
        β.val.inChart e.val z (Pi.basisFun ℂ (Fin 2))) : α = β := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt HeckeCycles.GeometricSource.CM.BallChart x
  have he : e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain := chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart x
  have hx : x ∈ e.source := mem_chart_source HeckeCycles.GeometricSource.CM.BallChart x
  have hy : e x ∈ e.target := e.map_source hx
  have hB : e x ∈ B.domain := by rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he] at hy
  let E : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart B.Domain := ⟨e, he⟩
  have h := (PureTopCoefficient.CM.pure_top_chart_from_coefficient α hα E (e x) hy).trans
    ((congrArg PureTopCoefficient.CM.ballAreaCoefficient (hcoeff E (e x) hB)).trans
      (PureTopCoefficient.CM.pure_top_chart_from_coefficient β hβ E (e x) hy).symm)
  have hp := congrArg (fun c : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2 =>
    c.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x)) h
  exact (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart_apply e he α.val hx).symm.trans
    (hp.trans (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart_apply e he β.val hx))

variable [IsGalois ℚ K] {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true)
  (D : SourceIntrinsicKernel.CM.SourceNativeThetaKernelData K Q hμ)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

include D hL in
theorem ball_top_eq_sum_source_wedges (Φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (s : ℂ)
    (α : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 α.val)
    (hcoeff : ∀ (e : SmoothTopology.CM.SmoothAtlasChart HeckeCycles.GeometricSource.CM.BallChart B.Domain) z, z ∈ B.domain →
      α.val.inChart e.val z (Pi.basisFun ℂ (Fin 2)) =
        s * InitialTensor.CM.splitThetaTopCoefficient K (L 0) (L 1) Φ z) :
    ∃ (c : ℂ) (n : ℕ) (φ ψ : Fin n → RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)),
      α = ∑ i, c • BallForms.CM.sourceBallTwoForm K (L 0) (L 1) (φ i) (ψ i) := by
  obtain ⟨c, _, n, φ, ψ, hc⟩ := IntrinsicSourceTotalFactorization.CM.native_source_total_coefficient_factorization K d Q hμ D L hL Φ
  let β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 :=
    ∑ i, (s * c) • BallForms.CM.sourceBallTwoForm K (L 0) (L 1) (φ i) (ψ i)
  have hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 β.val :=
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0).sum_mem (fun i _ =>
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0).smul_mem (s * c)
        (BallForms.CM.source_ball_two_pure K (L 0) (L 1) (φ i) (ψ i)))
  refine ⟨s * c, n, φ, ψ, pure_ball_top_eq_of_coefficients K α β hα hβ ?_⟩
  intro e z hz
  rw [hcoeff e z hz, hc ⟨z, hz⟩, Finset.mul_sum]
  change _ = TotalBallForms.CM.chartFormValue 2 e.val z β (Pi.basisFun ℂ (Fin 2))
  simp only [β, map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have he := BallForms.CM.source_ball_two_coefficient K (L 0) (L 1) (φ i) (ψ i) e.val e.property hz
  change s * (c * Slots.CM.sourceWedgeCoefficient K (L 0) (L 1) (φ i) (ψ i) z) =
    (s * c) * (BallForms.CM.sourceBallTwoForm K (L 0) (L 1) (φ i) (ψ i)).val.inChart e.val z _
  rw [he, mul_assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallWedgeDecomposition.CM
