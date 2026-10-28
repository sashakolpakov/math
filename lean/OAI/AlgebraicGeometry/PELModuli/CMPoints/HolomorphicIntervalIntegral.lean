import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Holomorphic Interval Integral -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicIntervalIntegral

noncomputable section

/-! Compact interval integration preserves complex differentiability
when the actual derivative is jointly continuous. -/

open Set Filter _root_.Metric _root_.MeasureTheory
open scoped _root_.Topology Interval

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem hasFDerivAt_intervalIntegral_of_compact
    (f : P → ℝ → V) (D : P → ℝ → P →L[ℂ] V)
    (U : Set P) (hU : IsOpen U) (a b : ℝ)
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ uIcc a b))
    (hD : ContinuousOn (Function.uncurry D) (U ×ˢ uIcc a b))
    (hd : ∀ p ∈ U, ∀ t ∈ uIcc a b, HasFDerivAt (fun q => f q t) (D p t) p)
    (p : P) (hp : p ∈ U) :
    HasFDerivAt (fun q => ∫ t in a..b, f q t) (∫ t in a..b, D p t) p := by
  let : ProperSpace P := FiniteDimensional.proper ℂ P
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p r).prod isCompact_uIcc).exists_bound_of_continuousOn
    (hD.mono (prod_mono hball Subset.rfl))
  have hfc (q : P) (hq : q ∈ U) : ContinuousOn (f q) (uIcc a b) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hq, ht⟩)
  have hdc : ContinuousOn (D p) (uIcc a b) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hp, ht⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := D) (bound := fun _ => C) (s := ball p r) (ball_mem_nhds p hr)
  · filter_upwards [hU.mem_nhds hp] with q hq
    exact ((hfc q hq).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact (hfc p hp).intervalIntegrable
  · exact (hdc.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Filter.Eventually.of_forall (fun t ht q hq =>
      hC (q, t) ⟨ball_subset_closedBall hq, uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t ht q hq =>
      hd q (hball (ball_subset_closedBall hq)) t (uIoc_subset_uIcc ht))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicIntervalIntegral
