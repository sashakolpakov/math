import OAI.Analysis.PDE.Concentration.SpatialCellL2
import OAI.Analysis.PDE.Concentration.Lattice.Smoothing

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current Set

theorem smoothedSquare_eq_sourceIntegral {d : ℕ} {h : ℝ} (hh : 0 < h)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    smoothedSquare h f x = ∫ y, ‖f (x - y)‖ ^ 2 ∂OAI.Analysis.Calculus.Current.sourceKernelMeasure d h := by
  rw [integral_sourceKernelMeasure h hh]
  change (∫ y, OAI.Analysis.Calculus.Current.smoothingKernel d h (x - y) * ‖f y‖ ^ 2) =
    ∫ y, OAI.Analysis.Calculus.Current.smoothingKernel d h y * ‖f (x - y)‖ ^ 2
  simpa only [sub_sub_cancel] using
    integral_sub_left_eq_self (fun y => OAI.Analysis.Calculus.Current.smoothingKernel d h y * ‖f (x - y)‖ ^ 2) volume x

theorem integral_smoothedSquare_eq_of_translate {d : ℕ} {h : ℝ} (hh : 0 < h)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (hf : Continuous f) {A : ℝ} (hA : ∀ x, ‖f x‖ ≤ A)
    {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)} (hS : volume S ≠ ⊤) {M : ℝ}
    (htranslate : ∀ y, (∫ x in S, ‖f (x - y)‖ ^ 2) = M) :
    (∫ x in S, smoothedSquare h f x) = M := by
  let := OAI.Analysis.Calculus.Current.sourceKernelMeasure_isProbability d h hh
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  have hc : Continuous (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d => ‖f (p.2 - p.1)‖ ^ 2) := by fun_prop
  have hi : Integrable (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d => ‖f (p.2 - p.1)‖ ^ 2)
      ((OAI.Analysis.Calculus.Current.sourceKernelMeasure d h).prod (volume.restrict S)) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (A ^ 2)
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (p.2 - p.1)‖)] using
      pow_le_pow_left₀ (norm_nonneg _) (hA (p.2 - p.1)) 2
  simp_rw [smoothedSquare_eq_sourceIntegral hh f]
  rw [← integral_integral_swap hi]
  simp_rw [htranslate]
  simp

theorem integrableOn_smoothedSquare {d : ℕ} {h : ℝ} (hh : 0 < h)
    (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (hf : Continuous f) {A : ℝ} (hA : ∀ x, ‖f x‖ ≤ A)
    {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)} (hS : volume S ≠ ⊤) :
    IntegrableOn (smoothedSquare h f) S := by
  let := OAI.Analysis.Calculus.Current.sourceKernelMeasure_isProbability d h hh
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  have hc : Continuous (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d => ‖f (p.2 - p.1)‖ ^ 2) := by fun_prop
  have hi : Integrable (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × OAI.Analysis.Calculus.Current.SpatialSpace d => ‖f (p.2 - p.1)‖ ^ 2)
      ((OAI.Analysis.Calculus.Current.sourceKernelMeasure d h).prod (volume.restrict S)) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (A ^ 2)
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (p.2 - p.1)‖)] using
      pow_le_pow_left₀ (norm_nonneg _) (hA (p.2 - p.1)) 2
  have he : smoothedSquare h f = fun x => ∫ y, ‖f (x - y)‖ ^ 2 ∂OAI.Analysis.Calculus.Current.sourceKernelMeasure d h :=
    funext (smoothedSquare_eq_sourceIntegral hh f)
  rw [IntegrableOn, he]
  exact hi.integral_prod_right

theorem finiteWave_translate {d : ℕ} {ι : Type*} [Fintype ι]
    (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ) (x y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    finiteWave ξ a (x - y) = finiteWave ξ (fun i => a i * planeWave (ξ i) (-y)) x := by
  unfold finiteWave
  apply Finset.sum_congr rfl
  intro i _
  rw [planeWave_sub]
  have he : Complex.exp (((-2 * Real.pi * inner ℝ y (ξ i) : ℝ) : ℂ) * Complex.I) =
      planeWave (ξ i) (-y) := by
    unfold planeWave
    rw [inner_neg_left]
    congr 2
    ring_nf
  rw [he]
  ring

theorem physicalSpatialCell_finite {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    volume (physicalSpatialCell R) ≠ ⊤ := by
  let K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d) := (fun q => spatialCellMap R (spatialFromCoordinates q)) ''
    Icc (0 : Option (Fin d) → ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image ((spatialCellMap R).continuous.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm.continuous)
  have hs : physicalSpatialCell R ⊆ K := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y.ofLp, ⟨fun i => (hy i).1.le, fun i => (hy i).2⟩, rfl⟩
  exact ne_top_of_le_ne_top hK.measure_ne_top (measure_mono hs)

theorem integral_smoothed_finiteWave {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : ι → Option (Fin d) → ℤ) (hinj : Function.Injective m) (a : ι → ℂ)
    (hm : ∀ j i, inner ℝ (ξ j) (R (EuclideanSpace.single i 1)) = (m j i : ℝ) / 100)
    {h : ℝ} (hh : 0 < h) :
    (∫ x in physicalSpatialCell R, smoothedSquare h (finiteWave ξ a) x) =
      ∫ x in physicalSpatialCell R, ‖finiteWave ξ a x‖ ^ 2 := by
  apply integral_smoothedSquare_eq_of_translate hh _ (continuous_finiteWave ξ a)
    (norm_finiteWave_le ξ a) (physicalSpatialCell_finite R)
  intro y
  simp_rw [finiteWave_translate ξ a]
  rw [integral_sq_physicalSpatialCell R ξ m hinj _ hm,
    integral_sq_physicalSpatialCell R ξ m hinj a hm]
  simp

end OAI.Analysis.PDE.Concentration
