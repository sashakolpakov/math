import OAI.Analysis.PDE.Dirichlet.Closed.JetCompactness
import OAI.Analysis.PDE.Dirichlet.LatticeUniformLimit
import OAI.Analysis.Normed.Function.Holder.C2HolderCompactLimit

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

/-- Compactness in the genuine lower-Hölder Banach norm, on the entire
closed periodic domain. Only the original smooth functions are assumed;
their limit is constructed using the closed derivative graph. -/
theorem exists_closed_banach_subsequence {E P V ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    (huper : ∀ k, LatticePeriodic e lat (u k))
    (Φ : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hΦ : ∀ k, ‖Φ k‖ ≤ M)
    (hv : ∀ k (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ k) x = u k x)
    (hG : ∀ k (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ k) x = fderiv ℝ (u k) x)
    (hH : ∀ k (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ k) x =
      fderiv ℝ (fderiv ℝ (u k)) x) :
    ∃ (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (α / 2)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα.le (Φ (φ k))) atTop (𝓝 g) := by
  have hb₀ (k x) (hx : r x ≤ 0) : ‖u k x‖ ≤ M := by
    rw [← hv k ⟨x, hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ k)).norm_coe_le_norm _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le (Φ k)).trans (hΦ k))
  have hb₁ (k x) (hx : r x ≤ 0) : ‖fderiv ℝ (u k) x‖ ≤ M := by
    rw [← hG k ⟨x, hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ k)).norm_coe_le_norm _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le (Φ k)).trans (hΦ k))
  have hb₂ (k x) (hx : r x ≤ 0) : ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M := by
    rw [← hH k ⟨x, hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM (Φ k)) ⟨x, hx⟩).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le (Φ k)).trans (hΦ k))
  have hholder (k x) (hx : r x ≤ 0) (y) (hy : r y ≤ 0) :
      ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤
        M * (dist x y) ^ α := by
    rw [← hH k ⟨x, hx⟩, ← hH k ⟨y, hy⟩]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder (Φ k) ⟨x, hx⟩ ⟨y, hy⟩).trans
      (mul_le_mul_of_nonneg_right (hΦ k) (Real.rpow_nonneg dist_nonneg _))
  obtain ⟨v, G, H, _, _, _, φ, hφ, hlv, hlG, hlH⟩ :=
    exists_jet_uniform_limit_on_regular_closed_domain hr hreg
      (isCompact_latticeSublevelCell e lat hK hr.continuous) inter_subset_right
      u hu hα hM hM hb₀ hb₁ hb₂ hholder
  have cv : CauchySeq (fun k ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ (φ k))) :=
    cauchySeq_bcf_of_lattice_uniform_limit e lat hrper hbounded _
      (fun k ↦ u (φ k)) (fun k ↦ huper (φ k)) (fun k ↦ hv (φ k)) v hlv
  have cG : CauchySeq (fun k ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ (φ k))) :=
    cauchySeq_bcf_of_lattice_uniform_limit e lat hrper hbounded _
      (fun k ↦ fderiv ℝ (u (φ k))) (fun k ↦ (huper (φ k)).fderiv)
      (fun k ↦ hG (φ k)) G hlG
  have cH : CauchySeq (fun k ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ (φ k))) :=
    cauchySeq_bcf_of_lattice_uniform_limit e lat hrper hbounded _
      (fun k ↦ fderiv ℝ (fderiv ℝ (u (φ k)))) (fun k ↦ (huper (φ k)).fderiv.fderiv)
      (fun k ↦ hH (φ k)) H hlH
  obtain ⟨g, hg⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.exists_lowerHalf_limit
    (isOpen_lt hr.continuous continuous_const) hα.le (fun k ↦ Φ (φ k)) hM
    (fun k ↦ hΦ (φ k)) cv cG cH
  exact ⟨g, φ, hφ, hg⟩

end OAI.Analysis.PDE.Dirichlet
