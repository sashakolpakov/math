import OAI.Analysis.PDE.Concentration.Periodized

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

theorem smoothingKernel_rotation {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h : ℝ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.smoothingKernel d h (R x) = OAI.Analysis.Calculus.Current.smoothingKernel d h x := by
  simp only [OAI.Analysis.Calculus.Current.smoothingKernel, OAI.Analysis.Calculus.Current.kernelProfile, norm_smul, R.norm_map]

def rotatedPeriodicSmoothingKernel {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h : ℝ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : ℝ :=
  periodicSmoothingKernel d h (R.symm x)

/-- Absolute kernel periodization on the source's rotated side-100 lattice.
No restriction to axis-aligned periods is made. -/
theorem rotated_periodized_kernel_le_smoothing {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {h : ℝ} (hh : 0 < h)
    {K : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ x, ‖K x‖ ≤ C * OAI.Analysis.Calculus.Current.smoothingKernel d h x) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    Summable (fun k : spatialIntegerLattice d => ‖K (x + (100 : ℝ) • R (k : OAI.Analysis.Calculus.Current.SpatialSpace d))‖) ∧
    ‖∑' k : spatialIntegerLattice d, K (x + (100 : ℝ) • R (k : OAI.Analysis.Calculus.Current.SpatialSpace d))‖ ≤
      C * rotatedPeriodicSmoothingKernel R h x := by
  have hb : ∀ y, ‖K (R y)‖ ≤ C * OAI.Analysis.Calculus.Current.smoothingKernel d h y := by
    intro y
    simpa only [smoothingKernel_rotation R] using hK (R y)
  have hh := periodized_kernel_le_smoothing hh hC hb (R.symm x)
  simpa only [map_add, map_smul, LinearIsometryEquiv.apply_symm_apply,
    rotatedPeriodicSmoothingKernel] using hh

end OAI.Analysis.PDE.Concentration
