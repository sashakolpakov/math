import OAI.Analysis.PDE.Concentration.Smoothing
import OAI.Analysis.Fourier.WavePackets.Poisson

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current Set
open scoped ContDiff

noncomputable def spatialIntegerLattice (d : ℕ) : Submodule ℤ (OAI.Analysis.Calculus.Current.SpatialSpace d) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Option (Fin d)) ℝ).toBasis)

instance (d : ℕ) : DiscreteTopology (spatialIntegerLattice d) := by
  unfold spatialIntegerLattice
  infer_instance

instance (d : ℕ) : IsZLattice ℝ (spatialIntegerLattice d) := by
  unfold spatialIntegerLattice
  infer_instance

theorem summable_spatial_lattice_weight (d N : ℕ) (hN : d + 1 < N) :
    Summable (fun k : spatialIntegerLattice d => ((1 + ‖k‖) ^ N)⁻¹) := by
  classical
  have hs0 : Summable (Pi.single (0 : spatialIntegerLattice d) (1 : ℝ)) :=
    (hasSum_single 0 (by intro k hk; simp [hk])).summable
  have hdim : Module.finrank ℤ (spatialIntegerLattice d) = d + 1 := by
    rw [ZLattice.rank ℝ]
    simp [OAI.Analysis.Calculus.Current.SpatialSpace]
  have hs := hs0.add (ZLattice.summable_norm_pow_inv (spatialIntegerLattice d) N (hdim ▸ hN))
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro k
  by_cases hk : k = 0
  · subst k
    simp only [norm_zero, add_zero, one_pow, inv_one, Pi.single_eq_same]
    exact le_add_of_nonneg_right (pow_nonneg (by simp) N)
  · simp only [Pi.single_eq_of_ne hk, zero_add]
    simpa only [inv_pow] using (inv_le_inv₀ (by positivity : 0 < (1 + ‖k‖) ^ N)
      (pow_pos (norm_pos_iff.mpr hk) N)).mpr
      (pow_le_pow_left₀ (norm_nonneg k) (by linarith [norm_nonneg k]) N)

theorem weighted_bracket_bound {s r D : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hD : 0 ≤ D) (h : 1 + s ≤ D * (1 + r)) (m : ℕ) :
    (1 + s) ^ (2 * m) * ((1 + r ^ 2) ^ m)⁻¹ ≤ D ^ (2 * m) * 2 ^ m := by
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + s) h (2 * m)
  have hq := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + r) ^ 2)
    (show (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) by nlinarith [sq_nonneg (r - 1)]) m
  rw [← pow_mul, mul_pow] at hq
  rw [mul_pow] at hp
  have hb := hp.trans (mul_le_mul_of_nonneg_left hq (pow_nonneg hD _))
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  nlinarith

theorem spatial_lattice_scaled_norm_bound {d : ℕ} {h : ℝ} (hh : 0 < h)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) (k : spatialIntegerLattice d) :
    1 + ‖k‖ ≤ ((1 + ‖x‖) * (1 + h)) *
      (1 + ‖h⁻¹ • (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))‖) := by
  let z := x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d)
  let r := ‖h⁻¹ • z‖
  have hr : 0 ≤ r := norm_nonneg _
  have hnorm : ‖k‖ ≤ ‖z‖ + ‖x‖ := by
    have ht := norm_sub_le z x
    have he : z - x = (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d) := by dsimp [z]; abel
    rw [he, norm_smul, Real.norm_eq_abs] at ht
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 100)] at ht
    have hk := norm_nonneg k
    change 100 * ‖k‖ ≤ ‖z‖ + ‖x‖ at ht
    linarith
  have hscale : ‖z‖ = h * r := by
    dsimp [r]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    field_simp
  rw [hscale] at hnorm
  change 1 + ‖k‖ ≤ (1 + ‖x‖) * (1 + h) * (1 + r)
  calc
    _ ≤ 1 + ‖x‖ + h * r := by linarith
    _ ≤ (1 + ‖x‖ + h * r) +
        (h + r + ‖x‖ * h + ‖x‖ * r + ‖x‖ * h * r) := le_add_of_nonneg_right (by positivity)
    _ = _ := by ring

theorem smoothing_translates_weight_bound {d : ℕ} {h : ℝ} (hh : 0 < h)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) (k : spatialIntegerLattice d) :
    OAI.Analysis.Calculus.Current.smoothingKernel d h (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d)) ≤
      (OAI.Analysis.Calculus.Current.kernelConstant d * (h ^ (d + 1))⁻¹ *
        ((1 + ‖x‖) * (1 + h)) ^ (2 * (d + 3)) * 2 ^ (d + 3)) *
      ((1 + ‖k‖) ^ (2 * (d + 3)))⁻¹ := by
  have hD : 0 ≤ (1 + ‖x‖) * (1 + h) := by positivity
  have hb := weighted_bracket_bound (norm_nonneg k) (norm_nonneg _) hD
    (spatial_lattice_scaled_norm_bound hh x k) (d + 3)
  have hmul := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (OAI.Analysis.Calculus.Current.kernelConstant_pos d).le (inv_nonneg.mpr (pow_nonneg hh.le (d + 1))))
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [OAI.Analysis.Calculus.Current.smoothingKernel, kernelProfile_eq_inv_pow,
    mul_assoc, mul_left_comm, mul_comm] using hmul

theorem summable_smoothing_translates {d : ℕ} {h : ℝ} (hh : 0 < h)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    Summable (fun k : spatialIntegerLattice d =>
      OAI.Analysis.Calculus.Current.smoothingKernel d h (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))) := by
  let C := OAI.Analysis.Calculus.Current.kernelConstant d * (h ^ (d + 1))⁻¹ *
    ((1 + ‖x‖) * (1 + h)) ^ (2 * (d + 3)) * 2 ^ (d + 3)
  exact ((summable_spatial_lattice_weight d (2 * (d + 3)) (by omega)).mul_left C).of_nonneg_of_le
    (fun k => (OAI.Analysis.Calculus.Current.smoothingKernel_pos d h hh _).le) (smoothing_translates_weight_bound hh x)

/-- The manuscript's positive kernel on the flat torus of side `100`,
represented as a periodic function on Euclidean spatial coordinates. -/
noncomputable def periodicSmoothingKernel (d : ℕ) (h : ℝ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : ℝ :=
  ∑' k : spatialIntegerLattice d, OAI.Analysis.Calculus.Current.smoothingKernel d h (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))

theorem periodicSmoothingKernel_nonneg {d : ℕ} {h : ℝ} (hh : 0 < h)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : 0 ≤ periodicSmoothingKernel d h x :=
  tsum_nonneg fun _ => (OAI.Analysis.Calculus.Current.smoothingKernel_pos d h hh _).le

theorem periodicSmoothingKernel_comparable {d : ℕ} {h : ℝ} (hh : 0 < h)
    {x y : OAI.Analysis.Calculus.Current.SpatialSpace d} (hxy : ‖x - y‖ ≤ h) :
    periodicSmoothingKernel d h x ≤ 3 ^ (d + 3) * periodicSmoothingKernel d h y := by
  unfold periodicSmoothingKernel
  rw [← tsum_mul_left]
  apply (summable_smoothing_translates hh x).tsum_le_tsum
    (fun k => smoothingKernel_comparable hh (by simpa only [add_sub_add_right_eq_sub] using hxy))
    ((summable_smoothing_translates hh y).mul_left _)

/-- A dominated inverse kernel can be periodized absolutely and is still
dominated by the actual periodic smoothing kernel. -/
theorem periodized_kernel_le_smoothing {d : ℕ} {h : ℝ} (hh : 0 < h)
    {K : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {C : ℝ} (_ : 0 ≤ C)
    (hK : ∀ x, ‖K x‖ ≤ C * OAI.Analysis.Calculus.Current.smoothingKernel d h x) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    Summable (fun k : spatialIntegerLattice d => ‖K (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))‖) ∧
    ‖∑' k : spatialIntegerLattice d, K (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))‖ ≤
      C * periodicSmoothingKernel d h x := by
  have hs := ((summable_smoothing_translates hh x).mul_left C).of_nonneg_of_le
    (fun k : spatialIntegerLattice d => norm_nonneg (K (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))))
    (fun k => hK _)
  refine ⟨hs, (norm_tsum_le_tsum_norm hs).trans ?_⟩
  unfold periodicSmoothingKernel
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum (fun k => hK _) ((summable_smoothing_translates hh x).mul_left C)

/-- The fixed-order semiclassical kernel lemma on the actual side-100
spatial torus. Its constant is independent of the symbol and of `h`. -/
theorem finite_order_periodized_kernel {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (B h : ℝ),
      ContDiff ℝ (2 * (d + 3) : ℕ) b → tsupport b ⊆ S → 0 ≤ B →
      (∀ j ≤ 2 * (d + 3), ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B) → 0 < h →
      ∀ x : OAI.Analysis.Calculus.Current.SpatialSpace d,
        Summable (fun k : spatialIntegerLattice d =>
          ‖scaledInverseKernel b h (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))‖) ∧
        ‖∑' k : spatialIntegerLattice d,
          scaledInverseKernel b h (x + (100 : ℝ) • (k : OAI.Analysis.Calculus.Current.SpatialSpace d))‖ ≤
          C * B * periodicSmoothingKernel d h x := by
  let C := (2 ^ (2 * (d + 3)) * (1 + 2 ^ (2 * (d + 3)) *
    (2 * (d + 3) + 1)) * volume.real S) / OAI.Analysis.Calculus.Current.kernelConstant d
  have hC : 0 ≤ C := by dsimp [C]; exact div_nonneg (by positivity) (OAI.Analysis.Calculus.Current.kernelConstant_pos d).le
  refine ⟨C, hC, ?_⟩
  intro b B h hb hs hB hderiv hh x
  exact periodized_kernel_le_smoothing hh (mul_nonneg hC hB)
    (finite_order_kernel_le_smoothing hS hb hs hB hderiv hh) x

end OAI.Analysis.PDE.Concentration
