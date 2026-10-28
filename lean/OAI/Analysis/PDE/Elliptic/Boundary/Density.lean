import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Hessian
import OAI.Analysis.PDE.Dirichlet.Continuity

/-! The equation extends to the flat boundary by continuity.  Its prescribed
log density has a genuine Lipschitz bound in chart coordinates. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem flat_boundary_mem_closure_halfBall {v z : E} (hv : ‖v‖ = 1)
    (hz : ‖z‖ < 1) (hvz : inner ℝ v z = 0) : z ∈ closure (openHalfBall v) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := min ((1 - ‖z‖) / 2) (ε / 2)
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have ht1 : t ≤ (1 - ‖z‖) / 2 := min_le_left _ _
  have ht2 : t ≤ ε / 2 := min_le_right _ _
  refine ⟨z + t • v, ⟨?_, ?_⟩, ?_⟩
  · have hn : ‖t • v‖ = t := by simp [norm_smul, abs_of_pos ht, hv]
    exact (norm_add_le _ _).trans_lt (by rw [hn]; linarith)
  · simp only [inner_add_right, real_inner_smul_right, hvz, real_inner_self_eq_norm_sq, hv]
    nlinarith
  · have hn : dist (z + t • v) z = t := by
      simp [dist_eq_norm, norm_smul, abs_of_pos ht, hv]
    simpa only [dist_comm z] using (hn.trans_lt (by linarith : t < ε))

omit [FiniteDimensional ℝ E] in
theorem log_density_chart_lipschitz {f : E → ℝ} {G : E → E} {S : Set E} {V W : ℝ}
    (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f (G z))
    (hG : ∀ z ∈ S, DifferentiableAt ℝ G z)
    (hne : ∀ z ∈ S, f (G z) ≠ 0)
    (hV : 0 ≤ V) (_ : 0 ≤ W)
    (hdf : ∀ z ∈ S, ‖fderiv ℝ f (G z)‖ / |f (G z)| ≤ V)
    (hdG : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ W)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S) :
    |Real.log (f (G z)) - Real.log (f (G z'))| ≤ V * W * ‖z - z'‖ := by
  have hd (y) (hy : y ∈ S) := ((hf y hy).hasFDerivAt.log (hne y hy)).comp y (hG y hy).hasFDerivAt
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy => (hd y hy).differentiableAt) _ hS hz' hz
  intro y hy
  rw [(hd y hy).fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  have hm := mul_le_mul (hdf y hy) (hdG y hy) (norm_nonneg _) hV
  simpa only [div_eq_mul_inv, mul_comm (|f (G y)|⁻¹)] using hm

theorem moore_equation_chart_boundary {n : ℕ}
    {u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hu : ContDiff ℝ 2 u) (hf : Continuous f) (hG : Continuous G)
    {v z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} (hv : ‖v‖ = 1) (hz : ‖z‖ < 1) (hvz : inner ℝ v z = 0)
    (heq : ∀ y ∈ openHalfBall v, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G y)) = f (G y)) :
    OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)) = f (G z) :=
  (Set.EqOn.closure heq ((OAI.Analysis.PDE.Dirichlet.continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots hu).comp hG) (hf.comp hG))
    (flat_boundary_mem_closure_halfBall hv hz hvz)

end OAI.Analysis.PDE.Elliptic
