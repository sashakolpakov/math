import OAI.Analysis.PDE.Schauder.Calculus.Schauder.LowerHolder
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MatrixInverse
import OAI.Analysis.Normed.Function.Holder.Banach.Polynomial
import OAI.Analysis.PDE.Dirichlet.Hessian

/-! The actual cutoff equation has Hölder forcing using only C² regularity of the solution. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def compactC1Holder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) : OAI.Analysis.Normed.Function.Holder.HolderMap E F α := by
  let C := (compact_C1_holder f hf hfc hα hα1).choose
  have hsup := (compact_C1_holder f hf hfc hα hα1).choose_spec.2.1
  have hholder := (compact_C1_holder f hf hfc hα hα1).choose_spec.2.2
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous C hsup)
    (by
      intro x y
      change ‖f x - f y‖ ≤ _
      simpa only [dist_eq_norm] using hholder x y)

@[simp] theorem compactC1Holder_value {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (x : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (compactC1Holder f hf hfc hα hα1) x = f x := by
  rfl

def cutoffCommutatorEntry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (v w x : E) : ℝ :=
  u x * fderiv ℝ (fderiv ℝ χ) x v w +
  fderiv ℝ χ x v * fderiv ℝ u x w + fderiv ℝ u x v * fderiv ℝ χ x w

theorem cutoff_hessian_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (v w x : E) :
    fderiv ℝ (fderiv ℝ (fun y => χ y * u y)) x v w =
      χ x * fderiv ℝ (fderiv ℝ u) x v w + cutoffCommutatorEntry χ u v w x := by
  rw [OAI.Analysis.PDE.Dirichlet.hessian_mul hχ hu]
  simp only [cutoffCommutatorEntry]
  ring

theorem contDiff_cutoffCommutatorEntry {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (hχ : ContDiff ℝ 3 χ) (hu : ContDiff ℝ 2 u) (v w : E) :
    ContDiff ℝ 1 (cutoffCommutatorEntry χ u v w) := by
  have hDχ : ContDiff ℝ 2 (fderiv ℝ χ) := hχ.fderiv_right (by norm_num)
  have hDDχ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ χ)) := hDχ.fderiv_right (by norm_num)
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  exact (((hu.of_le (by norm_num)).mul
    ((hDDχ.clm_apply contDiff_const).clm_apply contDiff_const)).add
    (((hDχ.of_le (by norm_num)).clm_apply contDiff_const).mul
      (hDu.clm_apply contDiff_const))).add
    ((hDu.clm_apply contDiff_const).mul
      ((hDχ.of_le (by norm_num)).clm_apply contDiff_const))

theorem hasCompactSupport_cutoffCommutatorEntry {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (hχc : HasCompactSupport χ) (v w : E) :
    HasCompactSupport (cutoffCommutatorEntry χ u v w) := by
  have hDD : HasCompactSupport (fun x => fderiv ℝ (fderiv ℝ χ) x v w) := by
    apply ((hχc.fderiv (𝕜 := ℝ)).fderiv_apply ℝ v).mono
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    rw [hx]
    rfl
  exact (hDD.mul_left.add ((hχc.fderiv_apply ℝ v).mul_right)).add
    ((hχc.fderiv_apply ℝ w).mul_left)

theorem nondivergence_cutoff {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator A (fun y => χ y * u y) x =
      χ x * nondivergenceOperator A u x +
        ∑ i, ∑ j, A x i j * cutoffCommutatorEntry χ u
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) x := by
  unfold nondivergenceOperator
  simp_rw [cutoff_hessian_entry χ u hχ hu, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end OAI.Analysis.PDE.Schauder
