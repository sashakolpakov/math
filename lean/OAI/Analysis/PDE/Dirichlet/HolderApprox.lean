import OAI.Analysis.Normed.Function.Holder.ScalarExtensionPeriodic
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationDerivatives

open Set Filter _root_.MeasureTheory Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

theorem smoothData_uniform_bound {m : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (x : EuclideanSpace ℝ (Fin m)) : |OAI.Analysis.PDE.Schauder.smoothData φ f x| ≤ B := by
  rw [← Real.norm_eq_abs]
  change ‖∫ y, φ.normed volume y * f (x - y)‖ ≤ B
  have h := norm_integral_le_of_norm_le (φ.integrable_normed.mul_const B)
    (Eventually.of_forall fun y ↦ show ‖φ.normed volume y * f (x - y)‖ ≤ φ.normed volume y * B from by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf _) (φ.nonneg_normed y))
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using h

theorem smoothData_tendstoUniformly {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    TendstoUniformly (fun j ↦ OAI.Analysis.PDE.Schauder.smoothData (OAI.Analysis.PDE.Schauder.standardMollifier m j) f) f atTop := by
  have ht : Tendsto (fun j ↦ H * (OAI.Analysis.PDE.Schauder.standardMollifier m j).rOut ^ α) atTop (𝓝 0) := by
    simpa using ((OAI.Analysis.PDE.Schauder.standardMollifier_radius_tendsto m).rpow_const_nhds_zero hα).const_mul H
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht (Iio_mem_nhds hε)] with j hj
  intro x
  have hlt := (OAI.Analysis.PDE.Schauder.smoothData_error (OAI.Analysis.PDE.Schauder.standardMollifier m j) f hf hH hα.le hh x).trans_lt hj
  simpa only [Real.dist_eq, abs_sub_comm] using hlt

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
theorem smoothData_latticePeriodic
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : LatticePeriodic e b f) :
    LatticePeriodic e b (OAI.Analysis.PDE.Schauder.smoothData φ f) := by
  intro x l
  rw [lattice_translate_eq]
  change (∫ y, φ.normed volume y * f (e.symm ((l : P), 0) + x - y)) =
    ∫ y, φ.normed volume y * f (x - y)
  apply integral_congr_ae
  filter_upwards with y
  have h := hf (x - y) l
  rw [lattice_translate_eq] at h
  rw [add_sub_assoc, h]

omit [Fintype ι] in
/-- Smooth periodic approximations of arbitrary closed-domain Hölder data.
Both uniform and Hölder bounds are retained with the original graph norm,
and convergence on the original set is uniform. -/
theorem exists_periodic_smooth_holder_approximation
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set (EuclideanSpace ℝ (Fin m))} [Nonempty K]
    (hK : LatticePeriodic e b (fun x ↦ x ∈ K))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α)
    (hf : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f))) :
    ∃ F : ℕ → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ j, ContDiff ℝ ∞ (F j)) ∧ (∀ j, LatticePeriodic e b (F j)) ∧
      (∀ j x, |F j x| ≤ ‖f‖) ∧
      (∀ j x y, |F j x - F j y| ≤ ‖f‖ * dist x y ^ α) ∧
      TendstoUniformly (fun j (y : K) ↦ F j y) (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) atTop := by
  obtain ⟨g, hgn, hgp, hgf⟩ := OAI.Analysis.Normed.Function.Holder.exists_periodic_scalar_holder_extension e b hK hα hα1 f hf
  let F : ℕ → EuclideanSpace ℝ (Fin m) → ℝ :=
    fun j ↦ OAI.Analysis.PDE.Schauder.smoothData (OAI.Analysis.PDE.Schauder.standardMollifier m j) (OAI.Analysis.Normed.Function.Holder.HolderMap.value g)
  have hgB (x) : |OAI.Analysis.Normed.Function.Holder.HolderMap.value g x| ≤ ‖f‖ := by
    have h : |OAI.Analysis.Normed.Function.Holder.HolderMap.value g x| ≤ ‖g‖ := by
      simpa only [Real.norm_eq_abs] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le g x
    exact h.trans hgn
  have hgH (x y) : |OAI.Analysis.Normed.Function.Holder.HolderMap.value g x - OAI.Analysis.Normed.Function.Holder.HolderMap.value g y| ≤ ‖f‖ * ‖x - y‖ ^ α := by
    have h := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le g x y
    rw [Real.norm_eq_abs, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right hgn (Real.rpow_nonneg (norm_nonneg _) _))
  refine ⟨F, fun j ↦ OAI.Analysis.PDE.Schauder.contDiff_smoothData _ _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value g).continuous,
    fun j ↦ smoothData_latticePeriodic e b _ _ hgp,
    fun j x ↦ smoothData_uniform_bound _ _ hgB x, ?_, ?_⟩
  · intro j x y
    simpa only [dist_eq_norm] using OAI.Analysis.PDE.Schauder.smoothData_holder (OAI.Analysis.PDE.Schauder.standardMollifier m j)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value g) (OAI.Analysis.Normed.Function.Holder.HolderMap.value g).continuous hgH x y
  · have ht := smoothData_tendstoUniformly (OAI.Analysis.Normed.Function.Holder.HolderMap.value g) (OAI.Analysis.Normed.Function.Holder.HolderMap.value g).continuous
      (norm_nonneg f) hα hgH
    have hs := ht.comp (fun y : K ↦ (y : EuclideanSpace ℝ (Fin m)))
    simpa only [F, Function.comp_def, hgf] using hs

end OAI.Analysis.PDE.Dirichlet
