import OAI.Analysis.PDE.Dirichlet.CellTransport
import Mathlib.Analysis.InnerProductSpace.Trace

open Set Filter InnerProductSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem indexedDivergence_eq_trace
    {H : EuclideanSpace ℝ I → EuclideanSpace ℝ I} {x : EuclideanSpace ℝ I}
    (hH : DifferentiableAt ℝ H x) :
    indexedDivergence H x =
      LinearMap.trace ℝ (EuclideanSpace ℝ I) (fderiv ℝ H x).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun I ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hd : fderiv ℝ (fun y ↦ H y i) x =
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ H x) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hH.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ H y i) x (EuclideanSpace.single i 1) = _
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul]
  rfl

/-- Divergence is unchanged by a constant invertible change of coordinates
when the vector flux is transformed contravariantly. The coordinate map
need not be an isometry; this is needed for arbitrary real lattices. -/
theorem indexedDivergence_linear_pullback
    (L : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ J)
    {H : EuclideanSpace ℝ J → EuclideanSpace ℝ J} {x : EuclideanSpace ℝ I}
    (hH : DifferentiableAt ℝ H (L x)) :
    indexedDivergence (fun y ↦ L.symm (H (L y))) x = indexedDivergence H (L x) := by
  have hd : HasFDerivAt (fun y ↦ L.symm (H (L y)))
      (L.symm.toContinuousLinearMap.comp ((fderiv ℝ H (L x)).comp L.toContinuousLinearMap)) x :=
    L.symm.hasFDerivAt.comp x (hH.hasFDerivAt.comp x L.hasFDerivAt)
  rw [indexedDivergence_eq_trace hd.differentiableAt,
    indexedDivergence_eq_trace hH, hd.fderiv]
  change LinearMap.trace ℝ (EuclideanSpace ℝ I)
    (L.symm.toLinearEquiv.conj (fderiv ℝ H (L x)).toLinearMap) = _
  exact LinearMap.trace_conj' _ _

end OAI.Analysis.PDE.Dirichlet
