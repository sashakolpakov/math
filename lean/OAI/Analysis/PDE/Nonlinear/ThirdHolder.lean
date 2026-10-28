import OAI.Analysis.PDE.Nonlinear.IndexedSchauder
import OAI.Analysis.PDE.Dirichlet.Moore.Matrix
import OAI.Analysis.PDE.Dirichlet.Derivative

/-! Hölder control of actual third derivatives after the first Moore bootstrap. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

theorem moore_directional_hessian_holder {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 3 u) (hf : ContDiff ℝ 2 f) (v x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) x -
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) y‖ ≤ C * ‖x - y‖ ^ α := by
  let A := fun x => OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)
  have hA : ContDiff ℝ 1 A :=
    (OAI.Analysis.PDE.Dirichlet.contDiff_mooreRealMatrix n 1).comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hu)
  have hw : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) v
  have hd : ContDiff ℝ 1 (OAI.Analysis.PDE.Dirichlet.directionalDerivative f v) := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hf (by norm_num) v
  have hAP : ∀ᶠ x in 𝓝 x₀, (A x).PosDef := by
    filter_upwards [hPD] with x hx
    exact OAI.Analysis.PDE.Dirichlet.mooreRealMatrix_posDef _ hx
  have heq : (fun x => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) =ᶠ[𝓝 x₀] f := hPDE
  have hEq : ∀ᶠ x in 𝓝 x₀,
      OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator A (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x = OAI.Analysis.PDE.Dirichlet.directionalDerivative f v x := by
    filter_upwards [heq.eventuallyEq_nhds] with x hx
    rw [OAI.Analysis.PDE.Dirichlet.mooreRealMatrix_linearization_at _ hw.contDiffAt]
    exact OAI.Analysis.PDE.Dirichlet.mooreLinearization_directional_eq hu v ((hf.differentiable (by norm_num)) x) hx
  exact indexed_C1_coefficient_schauder finProdFinEquiv hn hα hα1 A
    (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) (OAI.Analysis.PDE.Dirichlet.directionalDerivative f v) x₀ hA.contDiffAt hw hd.contDiffAt hAP hEq

theorem moore_directional_hessian_holder_local {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (v x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (hu : ContDiffAt ℝ 3 u x₀) (hf : ContDiffAt ℝ 2 f x₀)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) x -
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨g, hg, hgu⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hu
  obtain ⟨d, hd, hdf⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  have hHg : ∀ᶠ x in 𝓝 x₀, OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    filter_upwards [hgu.eventuallyEq_nhds] with x hx
    exact OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hx
  have hp : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) = d x := by
    filter_upwards [hHg, hdf, hPDE] with x hx hy hz
    rw [hx, hz, hy]
  have hpos : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x)).PosDef := by
    filter_upwards [hHg, hPD] with x hx hy
    rwa [hx]
  obtain ⟨r, hr, C, hC, hh⟩ := moore_directional_hessian_holder hn hα hα1 g d hg hd v x₀ hp hpos
  have hdir : OAI.Analysis.PDE.Dirichlet.directionalDerivative g v =ᶠ[𝓝 x₀] OAI.Analysis.PDE.Dirichlet.directionalDerivative u v := by
    filter_upwards [hgu.fderiv (𝕜 := ℝ)] with x hx
    exact congrArg (fun L => L v) hx
  obtain ⟨s, hs, hsame⟩ := Metric.eventually_nhds_iff.mp ((hdir.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  refine ⟨min r s, lt_min hr hs, C, hC, ?_⟩
  intro x hx y hy
  have hx' : x ∈ ball x₀ s := ball_subset_ball (min_le_right r s) hx
  have hy' : y ∈ ball x₀ s := ball_subset_ball (min_le_right r s) hy
  rw [← hsame hx', ← hsame hy']
  exact hh x (ball_subset_ball (min_le_left r s) hx) y (ball_subset_ball (min_le_left r s) hy)

end OAI.Analysis.PDE.Nonlinear
