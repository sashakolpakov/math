import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionChartDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Holomorphic Homeomorph Inverse -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicHomeomorphInverse.BundleCycles

noncomputable section

/-! A holomorphic homeomorphism with bijective complex differential has
a holomorphic inverse, proved in the actual preferred manifold charts. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionChartDerivative
open scoped _root_.Manifold ContDiff

variable {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem contMDiffAt_of_preferredChartMap {f : M → N} {x : M} {n : ℕ∞ω}
    (hc : ContinuousAt f x)
    (hf : ContDiffAt ℂ n (ComplexPoints.Analytic.ImmersionChartDerivative.preferredChartMap (E := E) (F := F) f x) (chartAt E x x)) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) n f x := by
  unfold ComplexPoints.Analytic.ImmersionChartDerivative.preferredChartMap at hf
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [ComplexPoints.Analytic.ImmersionChartDerivative.preferredChartMap, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id, contDiffWithinAt_univ] using hf

def homeomorphPreferredChart (e : M ≃ₜ N) (x : M) : OpenPartialHomeomorph E F :=
  ((chartAt E x).symm.transHomeomorph e).trans (chartAt F (e x))

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
theorem homeomorphPreferredChart_coe (e : M ≃ₜ N) (x : M) :
    (homeomorphPreferredChart (E := E) (F := F) e x : E → F) = ComplexPoints.Analytic.ImmersionChartDerivative.preferredChartMap e x := rfl

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
theorem homeomorphPreferredChart_source (e : M ≃ₜ N) (x : M) :
    chartAt E x x ∈ (homeomorphPreferredChart (E := E) (F := F) e x).source := by
  change chartAt E x x ∈ (chartAt E x).target ∧
    e ((chartAt E x).symm (chartAt E x x)) ∈ (chartAt F (e x)).source
  refine ⟨(chartAt E x).map_source (mem_chart_source E x), ?_⟩
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  exact mem_chart_source F (e x)

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
theorem homeomorphPreferredChart_center (e : M ≃ₜ N) (x : M) :
    homeomorphPreferredChart (E := E) (F := F) e x (chartAt E x x) = chartAt F (e x) (e x) := by
  change chartAt F (e x) (e ((chartAt E x).symm (chartAt E x x))) = _
  rw [(chartAt E x).left_inv (mem_chart_source E x)]

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
theorem homeomorphPreferredChart_symm (e : M ≃ₜ N) (x : M) :
    ComplexPoints.Analytic.ImmersionChartDerivative.preferredChartMap (E := F) (F := E) e.symm (e x) =
      (homeomorphPreferredChart (E := E) (F := F) e x).symm := by
  funext z
  change chartAt E (e.symm (e x)) (e.symm ((chartAt F (e x)).symm z)) =
    chartAt E x (e.symm ((chartAt F (e x)).symm z))
  rw [Homeomorph.symm_apply_apply]

omit [FiniteDimensional ℂ F] in
theorem holomorphicHomeomorph_inverse (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω e)
    (hd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x)) :
    ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ω e.symm := by
  let := FiniteDimensional.complete ℂ E
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  let q := homeomorphPreferredChart (E := E) (F := F) e x
  let a := chartAt E x x
  have ha : a ∈ q.source := homeomorphPreferredChart_source e x
  have hq : ContDiffAt ℂ ω q a := ComplexPoints.Analytic.ImmersionChartDerivative.contDiffAt_preferredChartMap (he x)
  have hb : Function.Bijective (fderiv ℂ q a) := by
    have h := ComplexPoints.Analytic.ImmersionChartDerivative.mfderiv_eq_preferredChartDerivative ((he x).mdifferentiableAt (by simp))
    exact (congrArg (fun l : E →L[ℂ] F => Function.Bijective l) h).mp (hd x)
  let l : E ≃L[ℂ] F := (LinearEquiv.ofBijective (fderiv ℂ q a).toLinearMap hb).toContinuousLinearEquiv
  have hderiv : HasFDerivAt q (l : E →L[ℂ] F) a := (hq.differentiableAt (by simp)).hasFDerivAt
  have hqi : ContDiffAt ℂ ω q.symm (q a) :=
    q.contDiffAt_symm (q.map_source ha)
      (by rw [q.left_inv ha]; exact hderiv) (by rw [q.left_inv ha]; exact hq)
  apply contMDiffAt_of_preferredChartMap e.symm.continuous.continuousAt
  rw [homeomorphPreferredChart_symm]
  exact (congrArg (fun z => ContDiffAt ℂ ω q.symm z) (homeomorphPreferredChart_center e x)).mp hqi

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicHomeomorphInverse.BundleCycles
