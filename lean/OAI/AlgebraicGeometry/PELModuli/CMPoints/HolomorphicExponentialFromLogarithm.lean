import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicInverseCoordinates
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt

/-! # Holomorphic Exponential From Logarithm -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicExponentialFromLogarithm

noncomputable section

/-! The actual continuous exponential is holomorphic near the identity
once its constructed logarithm is holomorphic. Both inverse equations
and the native identity derivative determine this same exponential. -/

open Set _root_.Metric Filter
open scoped _root_.Topology ContDiff

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

theorem exists_holomorphic_exponential_of_logarithm
    (f logarithm : P × V → V) (B : Set P) (hB : IsOpen B) (p₀ : P) (hp₀ : p₀ ∈ B)
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 < r)
    (hf : ContinuousAt f (p₀, 0)) (hfzero : ∀ p ∈ B, f (p, 0) = 0)
    (hfder : HasFDerivAt (fun v => f (p₀, v)) (ContinuousLinearMap.id ℝ V) 0)
    (hlog : DifferentiableOn ℂ logarithm (B ×ˢ ball 0 r))
    (hright : ∀ y ∈ ball 0 r, f (p₀, logarithm (p₀, y)) = y)
    (hleft : ∀ p ∈ B, ∀ v ∈ closedBall (0 : V) δ,
      f (p, v) ∈ closedBall (0 : V) (δ / 2) → logarithm (p, f (p, v)) = v) :
    ∃ U : Set (P × V), IsOpen U ∧ (p₀, (0 : V)) ∈ U ∧ DifferentiableOn ℂ f U := by
  let : CompleteSpace P := FiniteDimensional.complete ℂ P
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hlogzero (p : P) (hp : p ∈ B) : logarithm (p, 0) = 0 := by
    have h := hleft p hp 0 (mem_closedBall_self hδ.le)
    rw [hfzero p hp] at h
    exact h (mem_closedBall_self (half_pos hδ).le)
  have hzero : ∀ᶠ p in 𝓝 p₀, logarithm (p, 0) = 0 := by
    filter_upwards [hB.mem_nhds hp₀] with p hp
    exact hlogzero p hp
  have hlogC : ContDiffAt ℂ 1 logarithm (p₀, 0) :=
    Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt.Constructions.HolomorphicRegularity.contDiffAt_one_of_differentiableOn
      (hB.prod isOpen_ball) hlog ⟨hp₀, mem_ball_self hr⟩
  have hlogCont : ContinuousAt (fun y => logarithm (p₀, y)) (0 : V) :=
    hlogC.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  have hfd : HasFDerivAt (fun v => f (p₀, v))
      (ContinuousLinearEquiv.refl ℝ V).toContinuousLinearMap (logarithm (p₀, 0)) := by
    rw [hlogzero p₀ hp₀]
    exact hfder
  have hrightNear : ∀ᶠ y in 𝓝 (0 : V), f (p₀, logarithm (p₀, y)) = y := by
    filter_upwards [ball_mem_nhds (0 : V) hr] with y hy
    exact hright y hy
  have hvertical : HasFDerivAt (fun y => logarithm (p₀, y)) (ContinuousLinearMap.id ℝ V) 0 :=
    hfd.of_local_left_inverse hlogCont hrightNear
  have hfv : ∀ᶠ q in 𝓝 (p₀, (0 : V)), f q ∈ ball (0 : V) (δ / 2) := by
    apply hf.preimage_mem_nhds
    rw [hfzero p₀ hp₀]
    exact ball_mem_nhds (0 : V) (half_pos hδ)
  have hnear : ∀ᶠ q in 𝓝 (p₀, (0 : V)), logarithm (q.1, f q) = q.2 := by
    filter_upwards [(hB.prod isOpen_ball).mem_nhds
      (show (p₀, (0 : V)) ∈ B ×ˢ ball (0 : V) δ from ⟨hp₀, mem_ball_self hδ⟩), hfv] with q hq hfq
    exact hleft q.1 hq.1 q.2 (ball_subset_closedBall hq.2) (ball_subset_closedBall hfq)
  exact HolomorphicInverseCoordinates.exists_open_holomorphic_inverse_coordinates f logarithm p₀ hlogC hzero hvertical hf
    (hfzero p₀ hp₀) hnear

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicExponentialFromLogarithm
