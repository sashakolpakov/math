import OAI.Analysis.PDE.Schauder.Calculus.Interior.ThirdTensor
import OAI.Analysis.Normed.Function.Holder.C2HolderNorm

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Nonlinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance thirdJetFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdJetFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdJetThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdJetThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem norm_fderiv_directional_le (u : E → ℝ) (hu : ContDiff ℝ 2 u) (v x : E) :
    ‖fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x‖ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro z
  change ‖OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) z x‖ ≤ _
  rw [OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice hu]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ u) x z‖*‖v‖ := (fderiv ℝ (fderiv ℝ u) x z).le_opNorm v
    _ ≤ (‖fderiv ℝ (fderiv ℝ u) x‖*‖z‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ u) x).le_opNorm z) (norm_nonneg _)
    _ = _ := by ring

/-- A directional derivative's actual C²,α jet is controlled by the lower
jets of the original function and its actual third-derivative Hölder field.
The third-order norm is not assumed uniformly bounded. -/
theorem exists_directional_C2Holder {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    {α Q : ℝ} (hα : 0 ≤ α) (hQ : 0 ≤ Q) (u : E → ℝ) (hu : ContDiff ℝ 3 u)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hT : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x)
    (h₁ : ∀ x ∈ K, ‖fderiv ℝ u x‖ ≤ Q)
    (h₂ : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ Q)
    (v : E) (hv : ‖v‖ ≤ 1) :
    ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ‖U‖ ≤ Q+‖T‖ ∧
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = OAI.Analysis.PDE.Dirichlet.directionalDerivative u v x) ∧
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x) ∧
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) x) := by
  let w := OAI.Analysis.PDE.Dirichlet.directionalDerivative u v
  have hw : ContDiff ℝ 2 w := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) v
  have hw₀ : ∀ x ∈ K, ‖w x‖ ≤ Q := by
    intro x hx
    exact ((fderiv ℝ u x).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by simpa only [mul_one] using h₁ x hx))
  have hw₁ : ∀ x ∈ K, ‖fderiv ℝ w x‖ ≤ Q := by
    intro x hx
    exact (norm_fderiv_directional_le u (hu.of_le (by norm_num)) v x).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by simpa only [mul_one] using h₂ x hx))
  have hw₂ : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ ‖T‖ := by
    intro x hx
    rw [← OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu, ← hT ⟨x, hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.HolderMap.value T ⟨x,hx⟩).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans
        (by simpa only [mul_one] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T ⟨x,hx⟩))
  have hwh : ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ (fderiv ℝ w) x-fderiv ℝ (fderiv ℝ w) y‖ ≤ ‖T‖*(dist x y)^α := by
    intro x hx y hy
    rw [← OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu, ← OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu,
      ← hT ⟨x,hx⟩, ← hT ⟨y,hy⟩, ← sub_apply]
    exact ((OAI.Analysis.Normed.Function.Holder.HolderMap.value T ⟨x,hx⟩-OAI.Analysis.Normed.Function.Holder.HolderMap.value T ⟨y,hy⟩).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans
        (by simpa only [mul_one, Subtype.dist_eq] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T ⟨x,hx⟩ ⟨y,hy⟩))
  let U := OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff hΩ hΩK hα w hw hw₀ hw₁ hw₂ hwh
  refine ⟨U, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  apply OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα (add_nonneg hQ (norm_nonneg _))
  · intro x
    exact (hw₀ x x.property).trans (le_add_of_nonneg_right (norm_nonneg _))
  · intro x
    exact (hw₁ x x.property).trans (le_add_of_nonneg_right (norm_nonneg _))
  · intro x
    exact (hw₂ x x.property).trans (le_add_of_nonneg_left hQ)
  · intro x y
    exact (hwh x x.property y y.property).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hQ) (Real.rpow_nonneg dist_nonneg _))

end OAI.Analysis.PDE.Schauder
