import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Holomorphic Integral F -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicIntegralF.Constructions.HolomorphicIntegral

noncomputable section

/-!
# RiemannProjectivity: holomorphic parameter dependence of compact integrals

Joint continuity of a family and its complex derivative supplies a uniform
bound on a compact parameter neighborhood. Differentiation under the
integral then proves holomorphic dependence, with the actual integral of
the derivatives as derivative.
-/

open Set Filter _root_.Metric _root_.MeasureTheory
open scoped _root_.Topology

variable {V W K : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W]
  [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem hasFDerivAt_integral_of_compact (μ : Measure K) [IsFiniteMeasure μ]
    (F : V → K → W) (D : V → K → V →L[ℂ] W) {U : Set V}
    (hU : IsOpen U)
    (hF : ContinuousOn (fun p : V × K => F p.1 p.2) (U ×ˢ univ))
    (hD : ContinuousOn (fun p : V × K => D p.1 p.2) (U ×ˢ univ))
    (hder : ∀ x ∈ U, ∀ t, HasFDerivAt (fun y => F y t) (D x t) x)
    {x : V} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t, F y t ∂μ) (∫ t, D x t ∂μ) x := by
  let : ProperSpace V := FiniteDimensional.proper ℂ V
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  let : FiniteDimensional ℝ W := FiniteDimensional.trans ℝ ℂ W
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let A := closedBall x (r / 2)
  have hAU : A ⊆ U := fun y hy => hball
    ((mem_closedBall.mp hy).trans_lt (half_lt_self hr))
  have hxA : x ∈ A := mem_closedBall_self (half_pos hr).le
  have hA : A ∈ 𝓝 x := closedBall_mem_nhds x (half_pos hr)
  have hcompact : IsCompact (A ×ˢ (univ : Set K)) := (isCompact_closedBall _ _).prod isCompact_univ
  have hDC : ContinuousOn (fun p : V × K => D p.1 p.2) (A ×ˢ univ) :=
    hD.mono (prod_mono hAU Subset.rfl)
  obtain ⟨M, hM⟩ := (hcompact.image_of_continuousOn hDC).isBounded.exists_norm_le
  have hFcont (y : V) (hy : y ∈ U) : Continuous (F y) := by
    apply continuousOn_univ.mp
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t _ => ⟨hy, mem_univ t⟩)
  have hDcont : Continuous (D x) := by
    apply continuousOn_univ.mp
    exact hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t _ => ⟨hx, mem_univ t⟩)
  have hFint : Integrable (F x) μ := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ (hFcont x hx).continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := D) (bound := fun _ => M) hA
  · filter_upwards [hA] with y hy
    exact (hFcont y (hAU hy)).aestronglyMeasurable
  · exact hFint
  · exact hDcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t y hy => hM _ ⟨(y, t), ⟨hy, mem_univ t⟩, rfl⟩)
  · exact integrable_const M
  · exact Filter.Eventually.of_forall (fun t y hy => hder y (hAU hy) t)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicIntegralF.Constructions.HolomorphicIntegral
