import OAI.Analysis.PDE.Dirichlet.Path.Solution
import OAI.Analysis.PDE.Dirichlet.Path.Ellipticity
import OAI.Analysis.PDE.Dirichlet.Path.C1
import OAI.Analysis.PDE.Dirichlet.DensityPathLogLipschitz
import OAI.Analysis.PDE.Elliptic.Boundary.ClosedCompact
import OAI.Analysis.PDE.Elliptic.HessianNorm

open Set Module Metric InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The full closed-domain Hessian estimate along the actual affine density
path. Constants depend only on the fixed data and the compact observation
set, not on the path parameter or the particular smooth solution. -/
theorem uniform_closed_holder_densityPath_lattice {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef)
    {K' : Set (CoordinateSpace (n + 1) 4)} (hK' : IsCompact K')
    (hK'closed : K' ⊆ {x | r x ≤ 0}) :
    ∃ α D : ℝ, 0 < α ∧ α < 1 ∧ 0 < D ∧
      ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁, ∀ x ∈ K', ∀ y ∈ K',
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)) x -
          fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)) y‖ ≤ D * (dist x y) ^ α := by
  obtain ⟨A₀, G, hA₀, hG, hgrad⟩ := uniform_value_gradient_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨M, hM, hhess⟩ := uniform_hessian_bound_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨c, C, hc, hC, hell⟩ := uniform_ellipticity_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨m, U₀, L, hm, hU₀, hL, hdata⟩ := densityPath_uniform_bounds_lattice e lat hK
    hr.continuous hrper hbounded hne hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  obtain ⟨L₂, hL₂, hlog₂⟩ := densityPath_uniform_log_second_lattice e lat hK
    hr.continuous hrper hbounded hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  obtain ⟨R, hR, hRK⟩ := exists_compact_norm_bound
    (continuous_id : Continuous (fun x : CoordinateSpace (n + 1) 4 ↦ x)) hK'
  let U := ball (0 : CoordinateSpace (n + 1) 4) (R + 1)
  let S := closedBall (0 : CoordinateSpace (n + 1) 4) (R + 1) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_closedBall _ _).inter_right (isClosed_le hr.continuous continuous_const)
  have hKU : K' ⊆ U := by
    intro x hx
    change dist x 0 < R + 1
    rw [dist_zero_right]
    exact lt_of_le_of_lt (show ‖x‖ ≤ R from hRK x hx) (by linarith)
  have hUS : ∀ x ∈ U, r x ≤ 0 → x ∈ S := fun x hx hrx ↦ ⟨ball_subset_closedBall hx, hrx⟩
  obtain ⟨L₁, hL₁, hlog⟩ := densityPath_uniform_log_lipschitz_compact hS hF₀ hF₁
    (fun x hx ↦ hpos₀ x hx.2) (fun x hx ↦ hpos₁ x hx.2)
  let W := 1 + G + M + C + c + L / m
  have hLm : 0 ≤ L / m := div_nonneg hL.le hm.le
  have hW : 0 < W := by dsimp [W]; linarith
  have hGW : G ≤ W := by dsimp [W]; linarith
  have hMW : M ≤ W := by dsimp [W]; linarith
  have hCW : C ≤ W := by dsimp [W]; linarith
  have hcW : c ≤ W := by dsimp [W]; linarith
  have hLW : L / m ≤ W := by dsimp [W]; linarith
  let ψ := fun s : SmoothPathSolution e lat r B₀ F₀ F₁ ↦ fun x ↦ B₀ x + s.u x
  let f := fun s : SmoothPathSolution e lat r B₀ F₀ F₁ ↦ densityPath F₀ F₁ s.t
  have hψ (s) : ContDiff ℝ 4 (ψ s) := hB₀.add s.smooth
  have hψ₂ (s) : ContDiff ℝ 2 (ψ s) := (hψ s).of_le (by norm_num)
  have hfs (s) : ContDiff ℝ 2 (f s) := contDiff_densityPath hF₀ hF₁ s.t
  have hpc (s) : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (ψ s) x)).PosDef :=
    quaternionHessian_posDef_on_regular_sublevel (hr.of_le (by norm_num)) hreg (hψ₂ s)
      (hfs s).continuous (fun x hx ↦ densityPath_pos (hpos₀ x hx) (hpos₁ x hx) s.parameter)
      s.positive s.equation
  have hsell (s : SmoothPathSolution e lat r B₀ F₀ F₁) (x) (hx : r x ≤ 0) :=
    hell s.t s.parameter s.u s.smooth s.periodic s.zero s.positive s.equation x hx
  obtain ⟨α, D, hα, hα1, hD, hholder⟩ := OAI.Analysis.PDE.Elliptic.closed_hessian_holder_on_compact
    hr (hB₀.of_le (by norm_num)) (show IsOpen U from isOpen_ball) hK' hKU
    (fun x hx ↦ hK'closed hx) (fun x _ hx ↦ hreg x hx) hc hW hcW hL₁.le hL₂.le ψ f
    hψ (fun s ↦ (hfs s).continuous)
    (fun s x _ hx ↦ ((hgrad s.t s.parameter s.u s.smooth s.periodic s.zero s.positive
      s.equation x hx).2).trans hGW)
    (by
      intro s x _ hx
      rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient (hψ₂ s)]
      exact (hhess s.t s.parameter s.u s.smooth s.periodic s.zero s.positive s.equation x hx).trans hMW)
    (fun s x _ hx ↦ hpc s x hx)
    (fun s x _ hx ↦ (logRealOperator_norm_le_of_symbol _ hc.le hC.le (hsell s x hx)).trans hCW)
    (by intro s x _ hx w; rw [logRealOperator_symbol]; exact (hsell s x hx w).1)
    (fun s x _ _ ↦ (hfs s).differentiable (by norm_num) x)
    (fun s x _ hx ↦ (densityPath_pos (hpos₀ x hx) (hpos₁ x hx) s.parameter).ne')
    (by
      intro s x _ hx
      have hd := hdata s.t s.parameter x hx
      have hp := densityPath_pos (hpos₀ x hx) (hpos₁ x hx) s.parameter
      change ‖fderiv ℝ (densityPath F₀ F₁ s.t) x‖ / |densityPath F₀ F₁ s.t x| ≤ W
      rw [abs_of_pos hp]
      exact (div_le_div₀ hL.le hd.2.2 hm hd.1).trans hLW)
    (fun s x _ hx ↦ s.equation x hx)
    (fun s x hx y hy ↦ hlog s.t s.parameter x (hUS x hx.1 hx.2.le) y (hUS y hy.1 hy.2.le))
    (fun s x hx w ↦ hlog₂ s.t s.parameter x hx.2.le w)
    (by intro s x _ hx; change B₀ x + s.u x = B₀ x; rw [s.zero x hx, add_zero])
  refine ⟨α, D, hα, hα1, hD, ?_⟩
  intro s x hx y hy
  have hh := hholder s x hx y hy
  rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient_sub (hψ₂ s)] at hh
  simpa only [ψ, dist_eq_norm] using hh

end OAI.Analysis.PDE.Dirichlet
