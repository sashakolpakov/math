import OAI.Analysis.PDE.Dirichlet.JetCompactness
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Coefficient

/-! Bounded genuine Schauder jets pass to a pointwise limit without an assumed derivative limit. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

local instance limitFirstNG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance limitFirstNS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance limitSecondNG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance limitSecondNS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem contDiffOn_of_uniform_schauder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    {α C M₀ M₁ M₂ : ℝ} (hα : 0 < α)
    (h₀ : ∀ k x, x ∈ K → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, x ∈ K → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (hholder : ∀ k x, x ∈ K → ∀ y, y ∈ K →
      ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤ C * (dist x y) ^ α)
    (v : E → ℝ) (hv : ∀ x ∈ interior K, Tendsto (fun k => u k x) atTop (𝓝 (v x))) :
    ContDiffOn ℝ 2 v (interior K) ∧
      ∀ x ∈ interior K, ∀ y ∈ interior K,
        ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ C * (dist x y) ^ α := by
  classical
  obtain ⟨v₀, G₀, H₀, _, _, _, φ, hφ, _, hG₀, hH₀⟩ :=
    OAI.Analysis.PDE.Dirichlet.exists_jet_uniform_limit_on_compact_convex hK hconv u hu hα h₀ h₁ h₂ hholder
  let G : E → E →L[ℝ] ℝ := fun x => if hx : x ∈ K then G₀ ⟨x, hx⟩ else 0
  let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x => if hx : x ∈ K then H₀ ⟨x, hx⟩ else 0
  have hG : TendstoUniformlyOn (fun k => fderiv ℝ (u (φ k))) G atTop (interior K) := by
    intro U hU
    filter_upwards [hG₀ U hU] with k hk
    intro x hx
    simpa only [G, dite_eq_left (interior_subset hx)] using hk ⟨x, interior_subset hx⟩
  have hH : TendstoUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u (φ k)))) H atTop (interior K) := by
    intro U hU
    filter_upwards [hH₀ U hU] with k hk
    intro x hx
    simpa only [H, dite_eq_left (interior_subset hx)] using hk ⟨x, interior_subset hx⟩
  have hvs (x) (hx : x ∈ interior K) := (hv x hx).comp hφ.tendsto_atTop
  have hd := OAI.Analysis.PDE.Dirichlet.second_fderiv_of_locally_uniform_limit isOpen_interior
    (fun k => hu (φ k)) hvs hG.tendstoLocallyUniformlyOn hH.tendstoLocallyUniformlyOn
  refine ⟨OAI.Analysis.PDE.Dirichlet.contDiffOn_two_of_locally_uniform_derivatives isOpen_interior
    (fun k => hu (φ k)) hvs hG.tendstoLocallyUniformlyOn hH.tendstoLocallyUniformlyOn, ?_⟩
  intro x hx y hy
  rw [(hd x hx).2, (hd y hy).2]
  have hxlim : Tendsto (fun k => fderiv ℝ (fderiv ℝ (u (φ k))) x) atTop (𝓝 (H x)) := hH.tendsto_at hx
  have hylim : Tendsto (fun k => fderiv ℝ (fderiv ℝ (u (φ k))) y) atTop (𝓝 (H y)) := hH.tendsto_at hy
  have hn : Tendsto (fun k => ‖fderiv ℝ (fderiv ℝ (u (φ k))) x -
      fderiv ℝ (fderiv ℝ (u (φ k))) y‖) atTop (𝓝 ‖H x - H y‖) := by
    simpa using! (hxlim.sub hylim).norm
  exact le_of_tendsto hn
    (Eventually.of_forall (fun k => hholder (φ k) x (interior_subset hx) y (interior_subset hy)))

theorem norm_globalC2Value_le {m : ℕ} {α : ℝ} (u : GlobalC2Holder m α)
    (x : EuclideanSpace ℝ (Fin m)) : ‖globalC2Value u x‖ ≤ ‖u‖ :=
  ((OAI.Analysis.Normed.Function.Holder.C2Holder.value u).norm_coe_le_norm ⟨x, mem_univ x⟩).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le u)

theorem norm_fderiv_globalC2Value_le {m : ℕ} {α : ℝ} (u : GlobalC2Holder m α)
    (x : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ (globalC2Value u) x‖ ≤ ‖u‖ := by
  rw [globalC2Value_eq_extension, (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives isOpen_univ u (mem_univ x)).1]
  exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative u).norm_coe_le_norm ⟨x, mem_univ x⟩).trans
    (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le u)

theorem globalC2Holder_pointwise_limit {m : ℕ} {α M : ℝ} (hα : 0 < α)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : ℕ → GlobalC2Holder m α) (hbound : ∀ k, ‖u k‖ ≤ M)
    (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (hv : ∀ x ∈ interior K, Tendsto (fun k => globalC2Value (u k) x) atTop (𝓝 (v x))) :
    ContDiffOn ℝ 2 v (interior K) ∧
      ∀ x ∈ interior K, ∀ y ∈ interior K,
        ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ M * (dist x y) ^ α := by
  apply contDiffOn_of_uniform_schauder_bound hK hconv (fun k => globalC2Value (u k))
    (fun k => contDiff_globalC2Value (u k)) hα (M₀ := M) (M₁ := M) (M₂ := M)
  · exact fun k x _ => (norm_globalC2Value_le (u k) x).trans (hbound k)
  · exact fun k x _ => (norm_fderiv_globalC2Value_le (u k) x).trans (hbound k)
  · intro k x _
    rw [← globalHessianHolder_apply hα.le]
    exact ((OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le _ _).trans (norm_globalHessianHolder_le hα.le (u k))).trans (hbound k)
  · intro k x _ y _
    rw [← globalHessianHolder_apply hα.le, ← globalHessianHolder_apply hα.le]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le _ _ _).trans
      (mul_le_mul_of_nonneg_right ((norm_globalHessianHolder_le hα.le (u k)).trans (hbound k))
        (Real.rpow_nonneg dist_nonneg _))
  · exact hv

end OAI.Analysis.PDE.Schauder
