import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Compactness.Compact

/-! # Compact Integral -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CompactIntegral.Constructions.ExteriorCohomology

noncomputable section

/-!
# Compact-parameter integration for ExteriorCohomology

Joint continuity of the parameter derivatives on a compact integration space
gives a local uniform bound and justifies differentiation under the integral.
-/

open Set Filter _root_.MeasureTheory
open scoped _root_.Topology

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasure μ]

theorem hasFDerivAt_integral_compact
    {F : V → X → W} {F' : V → X → V →L[ℝ] W} {s : Set V} {v : V}
    (hs : IsOpen s) (hv : v ∈ s)
    (hF : ∀ a ∈ s, Continuous (F a))
    (hF' : ∀ a ∈ s, ∀ x, ContinuousAt (Function.uncurry F') (a, x))
    (hd : ∀ a ∈ s, ∀ x, HasFDerivAt (fun b => F b x) (F' a x) a) :
    HasFDerivAt (fun a => ∫ x, F a x ∂μ) (∫ x, F' v x ∂μ) v := by
  have hc : Continuous (F' v) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hF' v hv x).comp (continuousAt_const.prodMk continuousAt_id)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ᶠ a in 𝓝 v, ∀ x : X, ‖F' a x‖ ≤ C + 1 := by
    have he := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := v) (P := fun a x => ‖F' a x‖ ≤ C + 1) (fun x _ =>
        ((hF' v hv x).norm.eventually (gt_mem_nhds
          (lt_of_le_of_lt (hC x (mem_univ x)) (lt_add_one C)))).mono (fun _ h => h.le))
    simpa only [mem_univ, forall_true_left] using he
  obtain ⟨t, ht, htopen, hvt⟩ := mem_nhds_iff.mp hb
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := F')
    (bound := fun _ => C + 1) ((hs.inter htopen).mem_nhds ⟨hv, hvt⟩)
  · filter_upwards [hs.mem_nhds hv] with a ha
    exact ((hF a ha).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · exact (hF v hv).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · exact ae_of_all _ (fun x a ha => ht ha.2 x)
  · exact integrable_const _
  · exact ae_of_all _ (fun x a ha => hd a ha.1 x)

theorem integral_derivative_eq_zero_of_locally_constant_integral
    {F : V → X → W} {F' : V → X → V →L[ℝ] W} {s : Set V} {v : V} {c : W}
    (hs : IsOpen s) (hv : v ∈ s)
    (hF : ∀ a ∈ s, Continuous (F a))
    (hF' : ∀ a ∈ s, ∀ x, ContinuousAt (Function.uncurry F') (a, x))
    (hd : ∀ a ∈ s, ∀ x, HasFDerivAt (fun b => F b x) (F' a x) a)
    (hconst : ∀ a ∈ s, ∫ x, F a x ∂μ = c) :
    (∫ x, F' v x ∂μ) = 0 := by
  have hi := hasFDerivAt_integral_compact (μ := μ) hs hv hF hF' hd
  have he : (fun a => ∫ x, F a x ∂μ) =ᶠ[𝓝 v] fun _ => c := by
    filter_upwards [hs.mem_nhds hv] with a ha
    exact hconst a ha
  exact hi.unique ((hasFDerivAt_const c v).congr_of_eventuallyEq he)

end

end OAI.AlgebraicGeometry.AbelianVariety.CompactIntegral.Constructions.ExteriorCohomology
