import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Complex Chart Derivative -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartDerivative.Cycles

noncomputable section

/-!
# The actual complex derivative of a chart transition

For charts of a complex differentiable manifold, the transition map and
its inverse are differentiable on their actual open domains. Mathlib's
derivative of a differentiable open partial homeomorphism therefore supplies
a complex continuous linear equivalence. We identify its underlying map
with the ordinary Frechet derivative, including after centering a transition
at zero. Its real determinant is positive.
-/

open scoped _root_.Manifold

variable {E : Type} [NormedAddCommGroup E]
variable {M : Type} [TopologicalSpace M]
variable (e e' : OpenPartialHomeomorph M E)

/-- A point in both chart sources gives a point in the actual transition
domain after applying the first chart. -/
theorem complexChartTransition_mem_source (x : M) (hx : x ∈ e.source)
    (hx' : x ∈ e'.source) : e x ∈ (e.symm.trans e').source := by
  change e x ∈ e.target ∧ e.symm (e x) ∈ e'.source
  exact ⟨e.map_source hx, by simpa only [e.left_inv hx] using hx'⟩

/-- The transition in coordinates centered at `z` and its image. -/
def centeredComplexChartTransition (z : E) (v : E) : E :=
  (e.symm.trans e') (v + z) - (e.symm.trans e') z

@[simp]
theorem centeredComplexChartTransition_zero (z : E) :
    centeredComplexChartTransition e e' z 0 = 0 := by
  simp [centeredComplexChartTransition]

variable [NormedSpace ℂ E] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
variable (he : e ∈ atlas E M) (he' : e' ∈ atlas E M)

include he he' in
/-- Actual chart transitions and their inverses are complex differentiable
on their source and target. -/
theorem complexChartTransition_mdifferentiable :
    (e.symm.trans e').MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E) :=
  (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, E)) he).symm.trans
    (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, E)) he')

/-- The derivative of a complex chart transition is an actual invertible
complex continuous linear map. -/
def complexChartTransitionDerivative (z : E) (hz : z ∈ (e.symm.trans e').source) :
    E ≃L[ℂ] E :=
  (complexChartTransition_mdifferentiable e e' he he').mfderiv hz

/-- The equivalence has the ordinary Frechet derivative as its underlying
continuous linear map. -/
theorem complexChartTransitionDerivative_coe (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    (complexChartTransitionDerivative e e' he he' z hz : E →L[ℂ] E) =
      fderiv ℂ (e.symm.trans e') z :=
  mfderiv_eq_fderiv

/-- Differentiability of the actual transition with the specified
invertible derivative. -/
theorem complexChartTransition_hasFDerivAt (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    HasFDerivAt (e.symm.trans e')
      (complexChartTransitionDerivative e e' he he' z hz : E →L[ℂ] E) z := by
  rw [complexChartTransitionDerivative_coe]
  exact ((complexChartTransition_mdifferentiable e e' he he').mdifferentiableAt hz
    ).differentiableAt.hasFDerivAt

/-- Centering a genuine chart transition does not change its derivative. -/
theorem centeredComplexChartTransition_hasFDerivAt (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    HasFDerivAt (centeredComplexChartTransition e e' z)
      (complexChartTransitionDerivative e e' he he' z hz : E →L[ℂ] E) 0 := by
  change HasFDerivAt (fun v : E => (e.symm.trans e') (v + z) - (e.symm.trans e') z) _ 0
  have hd : HasFDerivAt (e.symm.trans e')
      (complexChartTransitionDerivative e e' he he' z hz : E →L[ℂ] E) (0 + z) := by
    simpa only [zero_add] using complexChartTransition_hasFDerivAt e e' he he' z hz
  simpa only [Function.comp_def, id_eq,
    ContinuousLinearMap.comp_id] using
    (hd.comp 0 ((hasFDerivAt_id (𝕜 := ℂ) (0 : E)).add_const z)).sub_const
      ((e.symm.trans e') z)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The derivative used for the local real homology comparison is the
restriction of the genuine complex derivative. -/
theorem centeredComplexChartTransition_hasRealFDerivAt (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    HasFDerivAt (centeredComplexChartTransition e e' z)
      ((complexChartTransitionDerivative e e' he he' z hz).restrictScalars ℝ : E →L[ℝ] E)
      0 :=
  (centeredComplexChartTransition_hasFDerivAt e e' he he' z hz).restrictScalars ℝ

/-- Every actual complex chart transition has positive real determinant
at every point of its transition domain. -/
theorem complexChartTransitionDerivative_realDet_pos (z : E)
    (hz : z ∈ (e.symm.trans e').source) :
    0 < LinearMap.det
      ((complexChartTransitionDerivative e e' he he' z hz).restrictScalars ℝ).toLinearMap :=
  ComplexOrientation.complexLinearEquiv_realDet_pos
    (complexChartTransitionDerivative e e' he he' z hz).toLinearEquiv

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartDerivative.Cycles
