import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CoefficientEnergyBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Schwartz
import OAI.Analysis.HodgeTheory.Decomposition.VectorEnergy

/-! # Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Bound

noncomputable section

/-! Genuine vector Sobolev coordinates of the original compact frame coefficients are bounded by the native bundle energy. -/

open _root_.TopologicalSpace _root_.MeasureTheory LineDeriv
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.VectorEnergy.Constructions

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def holomorphicLineFrameH1Smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ]
      Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1).comp
    ((Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i 1 f hf hs).comp (HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1).subtype)

def HolomorphicLineFrameH1Bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      ‖holomorphicLineFrameH1Smooth V e he i f hf hs a‖ ≤ K * ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖

theorem holomorphicLineFrameH1Smooth_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicLineFrameH1Bound V h := by
  intro e he i f hf hs
  have H := Holomorphic.CoefficientEnergyBound.holomorphicMetricFrameCoefficient_energy_bound V h e he i f hf hs
  let C := H.choose
  let D := H.choose_spec.choose
  have hC := H.choose_spec.choose_spec.1
  have hD := H.choose_spec.choose_spec.2.1
  have hb := H.choose_spec.choose_spec.2.2
  let b := stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let t : ℝ := C + Fintype.card (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) * D
  have ht : 0 ≤ t := add_nonneg hC (mul_nonneg (Nat.cast_nonneg _) hD)
  let B := Real.sqrt t
  let q : ℝ := 1 + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * Fintype.card (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V)
  have hq : 0 ≤ q := add_nonneg zero_le_one (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  refine ⟨B * q, mul_nonneg (Real.sqrt_nonneg t) hq, fun a => ?_⟩
  let w := Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i 1 f hf hs a.val
  let E := ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖
  have hn : ‖w.toLp 2 volume‖ ^ 2 ≤ C * E ^ 2 := by
    have heq := CoordinatesLp.holomorphicLineFrameCoefficientsLp_norm_sq V e he i 1 f hf hs a.val
    exact heq.trans_le (hb a).1
  have hd (j : Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) : ‖(∂_{b j} w).toLp 2 volume‖ ^ 2 ≤ D * E ^ 2 := by
    have heq : ‖(∂_{b j} w).toLp 2 volume‖ ^ 2 = ∫ z, ‖(∂_{b j} w) z‖ ^ 2 :=
      Analysis.HodgeTheory.Decomposition.CoordinateLp.Constructions.memLp_toLp_norm_sq _ ((∂_{b j} w).memLp 2 volume)
    apply heq.trans_le
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact (hb a).2 (b j) (b.norm_eq_one j)
  have hsum : (∑ j, ‖(∂_{b j} w).toLp 2 volume‖ ^ 2) ≤ Fintype.card (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) * (D * E ^ 2) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd j)
  have henergy : ‖w.toLp 2 volume‖ ^ 2 + (∑ j, ‖(∂_{b j} w).toLp 2 volume‖ ^ 2) ≤ (B * E) ^ 2 := by
    apply (add_le_add hn hsum).trans_eq
    calc
      _ = C * E ^ 2 + (Fintype.card (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) * D) * E ^ 2 :=
        congrArg (fun r : ℝ => C * E ^ 2 + r) (mul_assoc _ _ _).symm
      _ = t * E ^ 2 := (add_mul _ _ _).symm
      _ = _ := by rw [mul_pow, Real.sq_sqrt ht]
  have hv := Analysis.HodgeTheory.Decomposition.VectorEnergy.Constructions.vectorSchwartzSobolev_of_energy b w (B * E) (mul_nonneg (Real.sqrt_nonneg t) (norm_nonneg _)) henergy
  exact hv.trans_eq (mul_right_comm B E q)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Bound
