import OAI.Analysis.PDE.Nonlinear.JetExtension
import OAI.Analysis.PDE.Nonlinear.Bootstrap

/-! Interior C³ regularity of the actual Moore equation from local C²,α data. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

theorem moore_C3At_of_local_holder {n : ℕ} (hn : 3 ≤ n * 4) {α R C : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hu : ContDiffAt ℝ 2 u x₀) (hf : ContDiffAt ℝ 2 f x₀)
    (hR : 0 < R) (hC : 0 ≤ C)
    (hh : ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ContDiffAt ℝ 3 u x₀ := by
  obtain ⟨g, hg, _, hgu, V, H, hV, hH⟩ := exists_C2_holder_extension u x₀ hu hR hα.le hα1.le hC hh
  obtain ⟨d, hd, hdf, D, hD⟩ := exists_C2_compact_extension f x₀ hf hα.le hα1.le
  have hevent : ∀ᶠ x in 𝓝 x₀, g x = u x ∧ d x = f x ∧
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x ∧
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef := by
    filter_upwards [hgu, hdf, hPDE, hPD] with x hx hx' hpx hdx
    exact ⟨hx, hx', hpx, hdx⟩
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
  have hHg (x) (hx : x ∈ ball x₀ ε) :
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    apply OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (he hy).1
  have hc : ContDiffOn ℝ 3 g (ball x₀ ε) :=
    moore_C3_of_C2_holder hn hα hα1 g d hg (hd.of_le (by norm_num)) V H D hV hH hD isOpen_ball
      (by intro x hx; rw [hHg x hx, (he hx).2.2.1, (he hx).2.1])
      (by intro x hx; rw [hHg x hx]; exact (he hx).2.2.2)
  exact ((hc x₀ (mem_ball_self hε)).contDiffAt (ball_mem_nhds x₀ hε)).congr_of_eventuallyEq hgu.symm

theorem moore_C3On_of_holder {n : ℕ} (hn : 3 ≤ n * 4) {α C : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) {Ω : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hf : ContDiffOn ℝ 2 f Ω) (hC : 0 ≤ C)
    (hh : ∀ x ∈ Ω, ∀ y ∈ Ω,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ContDiffOn ℝ 3 u Ω := by
  intro x hx
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hpx : ∀ᶠ y in 𝓝 x, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y) = f y := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hPDE y hy
  have hdx : ∀ᶠ y in 𝓝 x, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)).PosDef := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hPD y hy
  exact (moore_C3At_of_local_holder hn hα hα1 u f x
    ((hu x hx).contDiffAt (hΩ.mem_nhds hx)) ((hf x hx).contDiffAt (hΩ.mem_nhds hx)) hR hC
    (fun y hy z hz => hh y (hRΩ hy) z (hRΩ hz)) hpx hdx).contDiffWithinAt

end OAI.Analysis.PDE.Nonlinear
