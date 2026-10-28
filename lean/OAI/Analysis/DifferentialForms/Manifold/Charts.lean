import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.Analysis.DifferentialForms.Manifold.Algebra
import OAI.Analysis.DifferentialForms.Manifold.SquareZero
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Charts -/

namespace OAI.Analysis.DifferentialForms.Manifold.Charts

noncomputable section

/-!
Exterior differentiation of actual manifold forms through smooth charts.
The chart-transition formulas are proved from the manifold chain rule.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual tangent map of a chart, with its vector-space target identified. -/
def chartTangentMap (e : OpenPartialHomeomorph M E) (x : M) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] E :=
  (NormedSpace.fromTangentSpace (e x)).toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x)

/-- The tangent map of the inverse chart, on the actual model tangent space. -/
def chartInverseTangentMap (e : OpenPartialHomeomorph M E) (y : E) :
    E →L[ℝ] TangentSpace 𝓘(ℝ, E) (e.symm y) :=
  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y).comp
    (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap

theorem chartInverseTangentMap_comp (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {x : M} (hx : x ∈ e.source) :
    (chartInverseTangentMap e (e x)).comp (chartTangentMap e x) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  have hd : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) := mdifferentiable_of_mem_atlas he
  ext v
  exact congrArg (fun f => f v) (hd.symm_comp_deriv hx)

theorem chartTangentMap_comp_inverse (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    (chartTangentMap e (e.symm y)).comp (chartInverseTangentMap e y) =
      ContinuousLinearMap.id ℝ E := by
  have hd : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) := mdifferentiable_of_mem_atlas he
  ext v
  exact congrArg (fun f => f v) (hd.comp_symm_deriv hy)

theorem fderiv_chart_transition (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source) :
    fderiv ℝ (f ∘ e.symm) y =
      (chartTangentMap f (e.symm y)).comp (chartInverseTangentMap e y) := by
  have ht := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) y
    (mdifferentiableAt_atlas (I := 𝓘(ℝ, E)) hf hfy)
    (mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E)) he hy)
  rw [mfderiv_eq_fderiv] at ht
  ext v
  exact congrArg (fun g => g v) ht

theorem contDiffAt_chart_transition (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) (hfy : e.symm y ∈ f.source) :
    ContDiffAt ℝ ∞ (f ∘ e.symm) y := by
  have he' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
  have hf' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f (e.symm y) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hf) hfy
  exact (hf'.comp y he').contDiffAt

end

end OAI.Analysis.DifferentialForms.Manifold.Charts
