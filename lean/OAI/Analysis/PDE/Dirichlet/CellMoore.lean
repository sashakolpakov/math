import OAI.Analysis.PDE.Dirichlet.CellTransport

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Variational OAI.Analysis.PDE.Weak OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Green

variable {m n : ℕ}

/-- The raw-cell variational operator with the concrete Moore cofactor
coefficients is exactly the Hessian linearization, not merely an operator
with the same principal symbol. -/
theorem cell_moore_flux_divergence
    (e : Fin (m + 1) ≃ Fin n × Fin 4)
    {ψ u : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ) (hu : ContDiff ℝ 2 u)
    (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Weak.classicalDivergence (fun y ↦
      cellMatrixCoefficient e (fun z ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z)) y
        (OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellEuclideanReindex e) y)) x =
      mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u (cellEuclideanReindex e x) := by
  have hA : ContDiff ℝ 1 (fun z ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z)) :=
    (contDiff_mooreRealMatrix n 1).comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hψ)
  have he : (fun y ↦
      cellMatrixCoefficient e (fun z ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z)) y
        (OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellEuclideanReindex e) y)) =
      (fun y ↦ coordinateReindex e.symm
        (indexedFlux (fun z ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z)) u
          (cellEuclideanReindex e y))) := by
    funext y
    exact cellMatrixCoefficient_gradient e _ (hu.differentiable (by norm_num) _)
  rw [he, classicalDivergence_reindex e
    ((contDiff_indexedFlux hA hu).differentiable one_ne_zero _)]
  exact moore_flux_divergence hψ hu _

/-- In particular, the minus sign in the weak divergence convention is
removed by supplying minus the desired right-hand side to the weak solver. -/
theorem moore_linearization_of_cell_equation
    (e : Fin (m + 1) ≃ Fin n × Fin 4)
    {ψ : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ)
    {v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hv : ContDiff ℝ 2 v)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} {g : ℝ}
    (heq : -OAI.Analysis.PDE.Weak.classicalDivergence (fun y ↦
      cellMatrixCoefficient e (fun z ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z)) y
        (OAI.Analysis.PDE.Variational.cellGradient v y)) x = -g) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ)
      (v ∘ (cellEuclideanReindex e).symm) (cellEuclideanReindex e x) = g := by
  have hu : ContDiff ℝ 2 (v ∘ (cellEuclideanReindex e).symm) :=
    hv.comp (cellEuclideanReindex e).symm.contDiff
  have hc : (v ∘ (cellEuclideanReindex e).symm) ∘ cellEuclideanReindex e = v := by
    funext y
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  have h := cell_moore_flux_divergence e hψ hu x
  rw [hc] at h
  exact h.symm.trans (neg_injective heq)

end OAI.Analysis.PDE.Dirichlet
