import OAI.Analysis.Normed.Function.Holder.C2HolderNorm

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem exists_holder_restriction {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K S : Set X} (hSK : S ⊆ K)
    {α : ℝ} (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap K F α) :
    ∃ g : OAI.Analysis.Normed.Function.Holder.HolderMap S F α, ‖g‖ ≤ ‖f‖ ∧
      ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value g x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f ⟨x,hSK x.property⟩ := by
  let ι : S → K := fun x => ⟨x,hSK x.property⟩
  have hι : Continuous ι := by fun_prop
  let v := BoundedContinuousFunction.ofNormedAddCommGroup (fun x : S => OAI.Analysis.Normed.Function.Holder.HolderMap.value f (ι x))
    ((OAI.Analysis.Normed.Function.Holder.HolderMap.value f).continuous.comp hι) ‖f‖ (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (ι x))
  have hh (x y : S) : ‖v x-v y‖ ≤ ‖f‖*dist x y^α := by
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (ι x) (ι y)
  let g := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hh
  refine ⟨g, ?_, fun _ => rfl⟩
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (norm_nonneg _) g
    (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (ι x)) hh

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance restrictionFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance restrictionFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance restrictionSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance restrictionSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Localize exact stored jets without any loss in their C²,α norm. -/
theorem exists_actual_C2Holder_restriction {Γ K S : Set E} {hΓK : Γ ⊆ K}
    (hSK : S ⊆ K) {α : ℝ} (hα : 0 ≤ α) (u : E → F) (hu : ContDiff ℝ 2 u)
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΓK α)
    (hU₀ : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x)
    (hU₁ : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x)
    (hU₂ : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) :
    ∃ V : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) (empty_subset S) α, ‖V‖ ≤ ‖U‖ ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.C2Holder.value V x = u x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative V x = fderiv ℝ u x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative V x = fderiv ℝ (fderiv ℝ u) x) := by
  have h₀ x (hx : x ∈ S) : ‖u x‖ ≤ ‖U‖ := by
    rw [← hU₀ ⟨x,hSK hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value U).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le U)
  have h₁ x (hx : x ∈ S) : ‖fderiv ℝ u x‖ ≤ ‖U‖ := by
    rw [← hU₁ ⟨x,hSK hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le U)
  have h₂ x (hx : x ∈ S) : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ‖U‖ := by
    rw [← hU₂ ⟨x,hSK hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le U.val.2.2 _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hh x (hx : x ∈ S) y (hy : y ∈ S) :
      ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ ‖U‖*dist x y^α := by
    rw [← hU₂ ⟨x,hSK hx⟩, ← hU₂ ⟨y,hSK hy⟩]
    exact OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder U _ _
  let V := OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff isOpen_empty (empty_subset S) hα u hu h₀ h₁ h₂ hh
  refine ⟨V, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  exact OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα (norm_nonneg _) V
    (fun x => h₀ x x.property) (fun x => h₁ x x.property) (fun x => h₂ x x.property)
    (fun x y => hh x x.property y y.property)

end OAI.Analysis.PDE.Schauder
