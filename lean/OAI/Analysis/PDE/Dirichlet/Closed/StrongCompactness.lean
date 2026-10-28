import OAI.Analysis.PDE.Dirichlet.Closed.BanachCompactness
import OAI.Analysis.Normed.Function.Holder.C2HolderStrongLimit

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

/-- Compactness loses an exponent for convergence, but not for the regularity
or quantitative bound of the resulting solution. -/
theorem exists_closed_strong_banach_subsequence {E P V ι : Type*}
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
    ∃ (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (φ : ℕ → ℕ), ‖g‖ ≤ M ∧ StrictMono φ ∧
      Tendsto (fun k ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα.le (Φ (φ k))) atTop
        (𝓝 (OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα.le g)) := by
  obtain ⟨g, φ, hφ, hlim⟩ := exists_closed_banach_subsequence e lat hK hr hrper
    hbounded hreg hα hM u hu huper Φ hΦ hv hG hH
  obtain ⟨g', hg', heq⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.exists_original_exponent_of_lowerHalf_limit hα.le hM
    (fun k ↦ Φ (φ k)) g (fun k ↦ hΦ (φ k)) hlim
  exact ⟨g', φ, hg', hφ, heq ▸ hlim⟩

end OAI.Analysis.PDE.Dirichlet
