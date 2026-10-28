import OAI.Analysis.PDE.Concentration.Cylinder.Calculus

namespace OAI.Analysis.PDE.Concentration

open Set Filter Laplacian InnerProductSpace
open scoped ContDiff Topology

theorem cylinder_laplacian_identity_on {f : CylinderSpace → ℝ} {U : Set CylinderSpace}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (t r θ : ℝ) (hr : r ≠ 0)
    (hp : cylinderPoint t r θ ∈ U) :
    deriv (deriv (fun s => f (cylinderPoint t s θ))) r +
      deriv (fun s => f (cylinderPoint t s θ)) r / r +
      deriv (deriv (fun s => f (cylinderPoint t r s))) θ / r ^ 2 +
      deriv (deriv (fun s => f (cylinderPoint s r θ))) t = Δ f (cylinderPoint t r θ) := by
  obtain ⟨F, V, hF, hV, hpV, _, hEq⟩ := exists_global_contDiff_two_eq_near hU hf hp
  have he : F =ᶠ[nhds (cylinderPoint t r θ)] f := eventuallyEq_of_mem (hV.mem_nhds hpV) hEq
  have her := he.comp_tendsto (hasDerivAt_cylinderPoint_radius t r θ).continuousAt
  have hea := he.comp_tendsto (hasDerivAt_cylinderPoint_angle t r θ).continuousAt
  have het := he.comp_tendsto (hasDerivAt_cylinderPoint_time t r θ).continuousAt
  simp only [Function.comp_def] at her hea het
  have h := cylinder_laplacian_identity hF t r θ hr
  rw [her.deriv.deriv_eq, her.deriv_eq, hea.deriv.deriv_eq, het.deriv.deriv_eq,
    (laplacian_congr_nhds he).self_of_nhds] at h
  exact h

end OAI.Analysis.PDE.Concentration
