import OAI.Analysis.PDE.Concentration.Lattice.Current

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current

def latticeIntegerVector {d : ℕ} (k : Option (Fin d) → ℤ) : OAI.Analysis.Calculus.Current.SpatialSpace d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm (fun i => (k i : ℝ))

def latticeWrap {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : OAI.Analysis.Calculus.Current.SpatialSpace d := R (spatialCubeVector (OAI.Analysis.Calculus.Current.wrapSpatial d (R.symm x)))

theorem latticeWrap_add_integer {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    latticeWrap R x + (100 : ℝ) • R (latticeIntegerVector (fun i => ⌊R.symm x i / 100⌋)) = x := by
  apply R.symm.injective
  simp only [map_add, map_smul, latticeWrap, ContinuousLinearEquiv.symm_apply_apply]
  ext i
  change 100 * Int.fract (R.symm x i / 100) + 100 * (⌊R.symm x i / 100⌋ : ℝ) = R.symm x i
  rw [Int.fract]
  ring

theorem latticeWrap_periodic_value {d : ℕ} {F : Type*}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (f : OAI.Analysis.Calculus.Current.SpatialSpace d → F)
    (hp : ∀ x k, f (x + (100 : ℝ) • R (latticeIntegerVector k)) = f x)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : f (latticeWrap R x) = f x := by
  calc
    _ = f (latticeWrap R x + (100 : ℝ) • R (latticeIntegerVector
        (fun i => ⌊R.symm x i / 100⌋))) := (hp _ _).symm
    _ = f x := congrArg f (latticeWrap_add_integer R x)

/-- Wrapping into an arbitrary side-100 lattice does not change the
convolution of a periodic field. No axis alignment is used. -/
theorem integral_latticeKernel_unwrap {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h : ℝ)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → F) (hf : Continuous f)
    (hp : ∀ x k, f (x + (100 : ℝ) • R (latticeIntegerVector k)) = f x) :
    (∫ t, f (R (spatialCubeVector t)) ∂latticeKernelMeasure R h) =
      ∫ x, f x ∂OAI.Analysis.Calculus.Current.sourceKernelMeasure d h := by
  calc
    _ = ∫ x, f (latticeWrap R x) ∂OAI.Analysis.Calculus.Current.sourceKernelMeasure d h := by
      simpa only [latticeKernelMeasure, latticeWrap, Function.comp_apply] using!
        integral_map (μ := OAI.Analysis.Calculus.Current.sourceKernelMeasure d h)
          (((OAI.Analysis.Calculus.Current.measurable_wrapSpatial d).comp R.symm.continuous.measurable).aemeasurable)
          ((hf.comp (R.continuous.comp (continuous_spatialCubeVector d))).aestronglyMeasurable)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (latticeWrap_periodic_value R f hp))

end OAI.Analysis.PDE.Concentration
