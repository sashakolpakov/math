import OAI.Analysis.PDE.Dirichlet.Path.FourthRegularity
import OAI.Analysis.PDE.Dirichlet.Fourth.LowerJets
import OAI.Analysis.Normed.Function.Holder.Banach.Interpolation
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tensor

/-! Closed C⁴ regularity of actual Banach path limits from uniform fourth
Hölder fields. The third-order estimate is already a consequence of the
fixed data and is not an additional hypothesis in the final theorem. -/
noncomputable section
open Set Module
open scoped ContDiff BoundedContinuousFunction
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance flG1 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] ℝ) := inferInstance
local instance flS1 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] ℝ) := inferInstance
local instance flG2 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance flS2 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance flG3 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance flS3 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance flG4 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance flS4 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance

theorem exists_holder_field_half_of_bounds {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α M : ℝ} (hα : 0 ≤ α) (hM : 0 ≤ M)
    (f : X → F) (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ M)
    (hh : ∀ x y, ‖f x-f y‖ ≤ M*dist x y^α) :
    ∃ U : OAI.Analysis.Normed.Function.Holder.HolderMap X F (α/2), (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x=f x) ∧ ‖U‖ ≤ 2*M := by
  obtain ⟨U,eU,hU⟩ := exists_holder_field_of_continuous_bounds hα hM f hf hb hh
  exact ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.lowerHalf hα U,eU,
    (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_lowerHalf_le_twice hα U).trans
      (mul_le_mul_of_nonneg_left hU (by norm_num))⟩

theorem BanachPathLimit.contDiffOn_four_closed_of_holder_fields
    (hn : 1 ≤ n) {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    {β t : ℝ} {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK β s t)
    (hr : ContDiff ℝ 3 r) (hB₀ : ContDiff ℝ 4 B₀)
    (hreg : ∀ x, r x=0 → fderiv ℝ r x ≠ 0)
    {γ M₃ M₄ : ℝ} (hγ : 0 < γ) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (hthird : ∀ a : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) γ,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+a.u y))) x) ∧ ‖T‖ ≤ M₃)
    (hfourth : ∀ a : SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound {x | r x ≤ 0} γ (fun y => B₀ y+a.u y) M₄) :
    ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x ≤ 0} := by
  have h₀ : ∀ j x, r x ≤ 0 → ‖B₀ x+(s j).u x‖ ≤ d.normBound := by
    intro j x hx
    rw [← d.jet_value (s j) ⟨x,hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value (d.jets (s j))).norm_coe_le_norm _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le _).trans (d.jet_norm _))
  have h₁ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fun y => B₀ y+(s j).u y) x‖ ≤ d.normBound := by
    intro j x hx
    rw [← d.jet_first (s j) ⟨x,hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (d.jets (s j))).norm_coe_le_norm _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le _).trans (d.jet_norm _))
  have h₂ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)) x‖ ≤ d.normBound := by
    intro j x hx
    rw [← d.jet_second (s j) ⟨x,hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM (d.jets (s j))) _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le _).trans (d.jet_norm _))
  apply L.contDiffOn_four_closed hn hr hB₀ hreg hγ
    d.normBound_pos.le d.normBound_pos.le hM₃ hM₄ h₀ h₁ h₂
  · intro j x hx
    obtain ⟨T,eT,hT⟩ := hthird (s j)
    rw [← eT ⟨x,hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T _).trans hT
  · intro j x hx
    obtain ⟨T,eT,hT⟩ := hfourth (s j)
    rw [← eT ⟨x,hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T _).trans hT
  · intro j x hx y hy
    obtain ⟨T,eT,hT⟩ := hthird (s j)
    rw [← eT ⟨x,hx⟩,← eT ⟨y,hy⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T _ _).trans
      (mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg dist_nonneg _))
  · intro j x hx y hy
    obtain ⟨T,eT,hT⟩ := hfourth (s j)
    rw [← eT ⟨x,hx⟩,← eT ⟨y,hy⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T _ _).trans
      (mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg dist_nonneg _))

end OAI.Analysis.PDE.Dirichlet
