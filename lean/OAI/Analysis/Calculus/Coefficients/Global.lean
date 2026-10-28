import OAI.Analysis.Calculus.Coefficients.Basic

open Set Filter _root_.MeasureTheory Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem smoothField_periodic
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (v : EuclideanSpace ℝ (Fin m))
    (hf : ∀ x, f (x+v)=f x) : ∀ x, smoothField φ f (x+v)=smoothField φ f x := by
  intro x
  simp only [smoothField_eq_integral]
  apply integral_congr_ae
  filter_upwards with y
  rw [show x+v-y=(x-y)+v by abel,hf]

omit [CompleteSpace F] in
theorem smoothField_latticePeriodic
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (smoothField φ f) := by
  intro x l
  rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq]
  rw [add_comm]
  apply smoothField_periodic φ f
  intro y
  have h := hf y l
  rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq] at h
  simpa only [add_comm] using h

/-- Global Banach-valued periodic Hölder fields have smooth periodic
approximations retaining their uniform and Hölder bounds. -/
theorem exists_periodic_smooth_field_approximation
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {α : ℝ} (hα : 0 < α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) F α)
    (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.HolderMap.value f)) :
    ∃ A : ℕ → EuclideanSpace ℝ (Fin m) → F,
      (∀ j, ContDiff ℝ ∞ (A j)) ∧ (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (A j)) ∧
      (∀ j x, ‖A j x‖ ≤ ‖f‖) ∧
      (∀ j x y, ‖A j x-A j y‖ ≤ ‖f‖*dist x y^α) ∧
      TendstoUniformly A (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) atTop := by
  have hH (x y : EuclideanSpace ℝ (Fin m)) :
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f x-OAI.Analysis.Normed.Function.Holder.HolderMap.value f y‖ ≤ ‖f‖*‖x-y‖^α := by
    simpa only [dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f x y
  refine ⟨fun j ↦ smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) (OAI.Analysis.Normed.Function.Holder.HolderMap.value f),
    fun j ↦ contDiff_smoothField _ _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value f).continuous,
    fun j ↦ smoothField_latticePeriodic e b _ _ hf,
    fun j x ↦ smoothField_uniform_bound _ _ (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f) x,?_,?_⟩
  · intro j x y
    simpa only [dist_eq_norm] using smoothField_holder _ _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value f).continuous hH x y
  · exact smoothField_tendstoUniformly _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value f).continuous (norm_nonneg f) hα hH

end OAI.Analysis.Calculus.Coefficients
