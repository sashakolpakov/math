import OAI.Analysis.Calculus.Coefficients.PeriodicMooreBarrierPositive
import OAI.Analysis.Calculus.Coefficients.Positive

open Set Filter Module Metric InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Retain convergence of the actual quaternionic Hessian, together with
the cofactor estimates obtained from the same smoothed potential. -/
theorem exists_periodic_smooth_hessian_cofactor_approximation
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hf : ContDiff ℝ 3 f) (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ u : ℕ → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j)) ∧ (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (u j)) ∧
      ∀ K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)
          (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f) atTop K ∧
        TendstoUniformlyOn (fun j x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
          (fun x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) atTop K ∧
        TendstoUniformlyOn (fun j x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
          (fun x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) atTop K ∧
        ∃ C : ℝ, 0 < C ∧
          (∀ j x, x ∈ K → ‖OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)‖ ≤ C) ∧
          (∀ j x, x ∈ K → ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)‖ ≤ C) ∧
          (∀ j x, x ∈ K → ∀ y, y ∈ K →
            ‖OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)-
              OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y)‖ ≤ C*dist x y^α) ∧
          (∀ j x, x ∈ K → ∀ y, y ∈ K →
            ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)-
              OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y)‖ ≤ C*dist x y^α) := by
  obtain ⟨u,hu,hup,hdata⟩ := exists_fourSlot_periodic_smooth_potential_approximation
    e b f hf hfp hα hα1
  refine ⟨u,hu,hup,?_⟩
  intro K hK
  obtain ⟨_,_,hc,B,hB,_,_,hBD,hBH⟩ := hdata K hK
  have hH := (quaternionHessian_composition_approximation
    (fun H : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦ H) contDiff_id u f
    (hf.of_le (by norm_num)) hK hc hB.le hBD hBH).1
  obtain ⟨hcM,M,hM,hMB,hMH⟩ := quaternionHessian_composition_approximation
    OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.contDiff_mooreRealMatrix n 1) u f
    (hf.of_le (by norm_num)) hK hc hB.le hBD hBH
  obtain ⟨hcA,A,hA,hAB,hAH⟩ := quaternionHessian_composition_approximation
    OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1) u f
    (hf.of_le (by norm_num)) hK hc hB.le hBD hBH
  refine ⟨hH,hcM,hcA,M+A,by positivity,?_,?_,?_,?_⟩
  · exact fun j x hx ↦ (hMB j x hx).trans (by linarith)
  · exact fun j x hx ↦ (hAB j x hx).trans (by linarith)
  · intro j x hx y hy
    exact (hMH j x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α))
  · intro j x hx y hy
    exact (hAH j x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α))

end OAI.Analysis.Calculus.Coefficients
