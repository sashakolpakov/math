import OAI.Analysis.PDE.Dirichlet.HolderApprox
import OAI.Analysis.PDE.Dirichlet.CoordinateTransport

open Set Filter _root_.MeasureTheory Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
/-- Smooth approximation commutes with an isometric change of coordinates.
In particular the estimate is in the physical norm, with no dimension factor. -/
theorem exists_isometric_periodic_smooth_holder_approximation {m : ℕ}
    (L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set E} [Nonempty K] (hK : LatticePeriodic e b (fun x ↦ x ∈ K))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α)
    (hf : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f))) :
    ∃ F : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (F j)) ∧ (∀ j, LatticePeriodic e b (F j)) ∧
      (∀ j x, |F j x| ≤ ‖f‖) ∧
      (∀ j x y, |F j x - F j y| ≤ ‖f‖ * dist x y ^ α) ∧
      TendstoUniformly (fun j (y : K) ↦ F j y) (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) atTop := by
  obtain ⟨g, hgn, hgp, hgf⟩ := OAI.Analysis.Normed.Function.Holder.exists_periodic_scalar_holder_extension e b hK hα hα1 f hf
  let g' : EuclideanSpace ℝ (Fin m) → ℝ := fun y ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value g (L.symm y)
  let e' : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P × V :=
    L.symm.toContinuousLinearEquiv.trans e
  have hgc : Continuous g' := (OAI.Analysis.Normed.Function.Holder.HolderMap.value g).continuous.comp L.symm.continuous
  have hgB (x) : |g' x| ≤ ‖f‖ := by
    have h : |g' x| ≤ ‖g‖ := by
      simpa only [g', Real.norm_eq_abs] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le g (L.symm x)
    exact h.trans hgn
  have hgH (x y) : |g' x - g' y| ≤ ‖f‖ * ‖x - y‖ ^ α := by
    have h := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le g (L.symm x) (L.symm y)
    rw [Real.norm_eq_abs, L.symm.isometry.dist_eq, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right hgn (Real.rpow_nonneg (norm_nonneg _) _))
  have hgp' : LatticePeriodic e' b g' := by
    intro x l
    simpa [e', g'] using hgp (L.symm x) l
  let G : ℕ → EuclideanSpace ℝ (Fin m) → ℝ := fun j ↦ OAI.Analysis.PDE.Schauder.smoothData (OAI.Analysis.PDE.Schauder.standardMollifier m j) g'
  let F : ℕ → E → ℝ := fun j x ↦ G j (L x)
  have hFp (j) : LatticePeriodic e b (F j) := by
    intro x l
    have h := smoothData_latticePeriodic e' b (OAI.Analysis.PDE.Schauder.standardMollifier m j) g' hgp' (L x) l
    simpa [e', F, G] using h
  refine ⟨F, fun j ↦ (OAI.Analysis.PDE.Schauder.contDiff_smoothData _ _ hgc).comp L.contDiff, hFp,
    fun j x ↦ smoothData_uniform_bound _ _ hgB (L x), ?_, ?_⟩
  · intro j x y
    have h := OAI.Analysis.PDE.Schauder.smoothData_holder (OAI.Analysis.PDE.Schauder.standardMollifier m j) g' hgc hgH (L x) (L y)
    simpa only [F, G, ← dist_eq_norm, L.isometry.dist_eq] using h
  · have ht := smoothData_tendstoUniformly g' hgc (norm_nonneg f) hα hgH
    have hs := ht.comp (fun y : K ↦ L y)
    simpa only [F, G, g', Function.comp_def, L.symm_apply_apply, hgf] using hs

omit [Fintype ι] in
/-- The approximation theorem in the quaternionic coordinates of the
nonlinear Dirichlet problem. -/
theorem exists_fourSlot_periodic_smooth_holder_approximation {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set (CoordinateSpace n 4)} [Nonempty K]
    (hK : LatticePeriodic e b (fun x ↦ x ∈ K))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α)
    (hf : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f))) :
    ∃ F : ℕ → CoordinateSpace n 4 → ℝ,
      (∀ j, ContDiff ℝ ∞ (F j)) ∧ (∀ j, LatticePeriodic e b (F j)) ∧
      (∀ j x, |F j x| ≤ ‖f‖) ∧
      (∀ j x y, |F j x - F j y| ≤ ‖f‖ * dist x y ^ α) ∧
      TendstoUniformly (fun j (y : K) ↦ F j y) (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) atTop :=
  exists_isometric_periodic_smooth_holder_approximation (flattenFourSlots n) e b hK hα hα1 f hf

end OAI.Analysis.PDE.Dirichlet
