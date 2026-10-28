import OAI.Analysis.PDE.Concentration.Lattice.Unwrap
import OAI.Analysis.PDE.Concentration.Recovery

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current

theorem latticeIntegerVector_neg {d : ℕ} (k : Option (Fin d) → ℤ) :
    latticeIntegerVector (-k) = -latticeIntegerVector k := by
  ext i
  simp [latticeIntegerVector]

theorem integral_sourceKernelMeasure {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : ℝ) (hh : 0 < h)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → F) :
    (∫ x, f x ∂OAI.Analysis.Calculus.Current.sourceKernelMeasure d h) = ∫ x, OAI.Analysis.Calculus.Current.smoothingKernel d h x • f x := by
  have hc : Continuous (OAI.Analysis.Calculus.Current.smoothingKernel d h) := by
    unfold OAI.Analysis.Calculus.Current.smoothingKernel
    exact continuous_const.mul ((OAI.Analysis.Calculus.Current.continuous_kernelProfile d).comp
      (show Continuous (fun x : OAI.Analysis.Calculus.Current.SpatialSpace d => h⁻¹ • x) by fun_prop))
  rw [OAI.Analysis.Calculus.Current.sourceKernelMeasure, integral_withDensity_eq_integral_toReal_smul
    hc.measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (OAI.Analysis.Calculus.Current.smoothingKernel_pos d h hh x).le]

theorem integral_latticeKernel_square {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {h : ℝ} (hh : 0 < h)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (hf : Continuous f)
    (hp : ∀ x k, f (x + (100 : ℝ) • R (latticeIntegerVector k)) = f x)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    (∫ t, ‖f (x - R (spatialCubeVector t))‖ ^ 2 ∂latticeKernelMeasure R h) =
      smoothedSquare h f x := by
  have hg : Continuous (fun y => ‖f (x - y)‖ ^ 2) := by fun_prop
  have hpg : ∀ y k,
      ‖f (x - (y + (100 : ℝ) • R (latticeIntegerVector k)))‖ ^ 2 = ‖f (x - y)‖ ^ 2 := by
    intro y k
    have he : x - (y + (100 : ℝ) • R (latticeIntegerVector k)) =
        (x - y) + (100 : ℝ) • R (latticeIntegerVector (-k)) := by
      rw [latticeIntegerVector_neg, map_neg, smul_neg]
      abel
    rw [he, hp]
  rw [integral_latticeKernel_unwrap R h _ hg hpg, integral_sourceKernelMeasure h hh]
  change (∫ y, OAI.Analysis.Calculus.Current.smoothingKernel d h y * ‖f (x - y)‖ ^ 2) =
    ∫ y, OAI.Analysis.Calculus.Current.smoothingKernel d h (x - y) * ‖f y‖ ^ 2
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y => OAI.Analysis.Calculus.Current.smoothingKernel d h y * ‖f (x - y)‖ ^ 2) volume x).symm

end OAI.Analysis.PDE.Concentration
