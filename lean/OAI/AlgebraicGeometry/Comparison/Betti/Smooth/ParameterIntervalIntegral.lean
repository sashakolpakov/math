import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Parameter Interval Integral -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ParameterIntervalIntegral.Dolbeault

noncomputable section

/-! Differentiation of a compact interval integral with finite-dimensional
real parameters and Banach-space coefficients. Joint continuity gives
the required domination on an actual compact parameter neighborhood. -/

open Set Filter _root_.Metric _root_.MeasureTheory
open scoped _root_.Topology Interval

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_parameter_intervalIntegral
    {g : P → ℝ → F} {g' : P → ℝ → P →L[ℝ] F} {S : Set P}
    (hS : IsOpen S) {p : P} (hp : p ∈ S) {a b : ℝ}
    (hg : ContinuousOn (Function.uncurry g) (S ×ˢ uIcc a b))
    (hg' : ContinuousOn (Function.uncurry g') (S ×ˢ uIcc a b))
    (hD : ∀ q ∈ S, ∀ t ∈ uIcc a b, HasFDerivAt (fun x => g x t) (g' q t) q) :
    HasFDerivAt (fun q => ∫ t in a..b, g q t) (∫ t in a..b, g' p t) p := by
  let : ProperSpace P := FiniteDimensional.proper ℝ P
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds hp)
  have hK : IsCompact (closedBall p r ×ˢ uIcc a b) :=
    (isCompact_closedBall p r).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hg'.mono (prod_mono hball Subset.rfl))
  have hgc (q : P) (hq : q ∈ S) : ContinuousOn (g q) (uIcc a b) :=
    hg.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hq, ht⟩)
  have hg'c : ContinuousOn (g' p) (uIcc a b) :=
    hg'.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hp, ht⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume) (F := g) (F' := g')
    (s := ball p r) (bound := fun _ => C) (ball_mem_nhds p hr) ?_
    (hgc p hp).intervalIntegrable ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hS.mem_nhds hp] with q hq
    exact ((hgc q hq).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact (hg'c.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall (fun t ht q hq =>
      hC (q, t) ⟨ball_subset_closedBall hq, uIoc_subset_uIcc ht⟩)
  · exact Eventually.of_forall (fun t ht q hq =>
      hD q (hball (ball_subset_closedBall hq)) t (uIoc_subset_uIcc ht))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ParameterIntervalIntegral.Dolbeault
