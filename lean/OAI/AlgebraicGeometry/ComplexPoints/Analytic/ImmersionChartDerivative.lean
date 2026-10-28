import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Immersion Chart Derivative -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionChartDerivative

noncomputable section

/-!
# Derivatives in the preferred charts of a manifold without boundary

These statements identify the coordinate derivative with the actual manifold
derivative. In particular, injectivity of the latter is the precise hypothesis
needed when applying the inverse function theorem in the preferred charts.
-/

open scoped _root_.Manifold ContDiff
open ChartedSpace

variable {K E F M N : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

/-- The map written in the preferred source and target charts. -/
def preferredChartMap (f : M → N) (x : M) : E → F :=
  fun z ↦ chartAt F (f x) (f ((chartAt E x).symm z))

/-- With self models, manifold regularity is ordinary regularity in charts. -/
theorem contDiffAt_preferredChartMap {f : M → N} {x : M} {r : ℕ∞ω}
    (hf : ContMDiffAt 𝓘(K, E) 𝓘(K, F) r f x) :
    ContDiffAt K r (preferredChartMap (E := E) (F := F) f x) (chartAt E x x) := by
  unfold preferredChartMap
  simpa only [extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id, contDiffWithinAt_univ]
    using (contMDiffAt_iff.mp hf).2

set_option backward.isDefEq.respectTransparency false in
/-- The actual manifold derivative is the coordinate Fréchet derivative. -/
theorem mfderiv_eq_preferredChartDerivative {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(K, E) 𝓘(K, F) f x) :
    (show E →L[K] F from mfderiv 𝓘(K, E) 𝓘(K, F) f x) =
      fderiv K (preferredChartMap (E := E) (F := F) f x) (chartAt E x x) := by
  unfold preferredChartMap
  simpa only [writtenInExtChartAt, extChartAt_coe,
    extChartAt_coe_symm, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, Set.range_id, fderivWithin_univ] using hf.mfderiv_abuse

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness and an injective manifold derivative give the injective
coordinate derivative required for a local immersion normal form. -/
theorem preferredChartDerivative_injective {f : M → N} {x : M} {r : ℕ∞ω}
    (hf : ContMDiffAt 𝓘(K, E) 𝓘(K, F) r f x) (hr : r ≠ 0)
    (hinj : Function.Injective (mfderiv 𝓘(K, E) 𝓘(K, F) f x)) :
    Function.Injective (fderiv K (preferredChartMap (E := E) (F := F) f x) (chartAt E x x)) := by
  rw [← mfderiv_eq_preferredChartDerivative (hf.mdifferentiableAt hr)]
  exact hinj

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionChartDerivative
