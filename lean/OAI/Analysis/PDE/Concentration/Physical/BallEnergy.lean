import OAI.Analysis.PDE.Concentration.BallEnergy
import OAI.Analysis.PDE.Concentration.Packet.Fiber
import OAI.Analysis.PDE.Dirichlet.PositiveDeterminant

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem spatial_background_trace_upper (d : ℕ) (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0)
    (hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    (∑ i, (spatialBackgroundMatrix d τ q i i).re) ≤ 3 := by
  have he := (finSuccEquiv d).sum_comp (fun i => (OAI.Analysis.Calculus.Current.physicalBackgroundHessian τ q i i).re)
  simpa only [spatialBackgroundMatrix, Matrix.submatrix_apply, he] using
    (OAI.Analysis.Calculus.Current.physicalBackgroundHessian_trace_bounds a τ q hY hr).2

/-- Pointwise output-energy gain for the literal physical packet current and
background. Background rank one, its uniform trace bound, and strict
ellipticity from the regularized density are derived here. -/
theorem exists_physical_ball_energy_lower (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
      (h a : ℝ), 0 < h → 0 < a → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3), a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ →
      ∀ (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3) (lam m : ℝ), 0 < lam → 0 ≤ m → m ≤ lam ^ (n + 1) →
      Metric.closedBall x₀ h ⊆
        {y | spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0} →
      ∀ (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ),
      ContDiffOn ℝ 2 u (Metric.ball x₀ h) → ContinuousOn u (Metric.closedBall x₀ h) →
      (∀ x ∈ Metric.closedBall x₀ h, u x ≤ 0) →
      (∀ x ∈ Metric.ball x₀ h, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) y + u y) x)).PosSemidef) →
      (∀ x ∈ Metric.ball x₀ h, OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) y + u y) x) =
        lam * (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re) →
      (∀ x ∈ Metric.ball x₀ h,
        m ≤ (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re) →
      c * h ^ 2 * m ^ (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤
        (-u x₀) * (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x₀) 0 0).re := by
  obtain ⟨c, hc, hb⟩ := exists_ball_energy_lower n (C := 3) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro R h a hh ha ι _ κ cR cI v z ht x₀ lam m hlam hm hml hball u hu huc hu0 hPSD hPDE hμ
  let B := fun y => lam * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) y
  let μ := fun y => (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y) 0 0).re
  have hreg (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3) (hx : x ∈ Metric.closedBall x₀ h) :
      OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) x ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain (OAI.Analysis.PDE.Green.energyComplexTime z) :=
    OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a (OAI.Analysis.PDE.Green.energyComplexTime z) ha ht
      ((show spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 from hball hx).le.trans (by norm_num))
  have hBa (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3) (hx : x ∈ Metric.closedBall x₀ h) :
      ContDiffAt ℝ 2 B x := contDiffAt_const.mul
        (spatial_functions_contDiffAt (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x (hreg x hx)).2
  apply hb x₀ h lam m hh hlam hm hml B u μ
    (fun x hx => (hBa x (Metric.ball_subset_closedBall hx)).contDiffWithinAt) hu
    (fun x hx => (hBa x hx).continuousAt.continuousWithinAt) huc
  · intro x hx
    apply OAI.Analysis.PDE.Dirichlet.complexify_posDef_of_posSemidef_mooreDet_pos _ (hPSD x hx)
    rw [hPDE x hx]
    apply mul_pos hlam
    apply physicalLatticeCurrent_time_pos R h a hh ha.ne' κ cR cI v
    · rw [physicalToNullCurrentPoint_fiber_imaginary]
      exact (hreg x (Metric.ball_subset_closedBall hx)).1
    · rw [physicalToNullCurrentPoint_fiber_imaginary]
      exact (show spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 from
        hball (Metric.ball_subset_closedBall hx)).le
  · intro x hx
    have hr := hreg x (Metric.ball_subset_closedBall hx)
    obtain ⟨w, hw⟩ := spatial_background_outer (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z)
      (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) x) hr.1
    refine ⟨w, ?_, ?_⟩
    · have hs := (spatial_functions_contDiffAt (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x hr).2
      have he := quaternionHessian_linear_combination_at OAI.Analysis.Calculus.Quaternion.threeSlots
        (f := fun _ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 => (0 : ℝ)) contDiffAt_const hs 0 lam
      simp only [zero_mul, zero_add, zero_smul] at he
      change OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => lam * spatialBackgroundFunction (n + 1)
        (OAI.Analysis.PDE.Green.energyComplexTime z) y) x = _
      rw [he, quaternionHessian_spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) x hr.1, hw]
    · rw [← hw]
      exact spatial_background_trace_upper (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) _ hr.1
        (show spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 from
          (show spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 from
            hball (Metric.ball_subset_closedBall hx)).le)
  · exact hPDE
  · exact hμ
  · intro x hx
    exact hu0 x (by simpa only [Metric.mem_closedBall, dist_eq_norm, hx] using (le_refl h))

end OAI.Analysis.PDE.Concentration
