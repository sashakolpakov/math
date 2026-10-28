import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CompactLimit
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformEstimate

/-! Uniform frozen-coefficient estimates give actual C² regularity of a pointwise limit. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

theorem cutoff_limit_C2_of_uniform_equations {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    (U : ℕ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : ℕ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hU : ∀ k x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (U k) x = u k x)
    (hV : ∀ k x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (V k) x = fderiv ℝ (u k) x)
    (B : ℕ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : ℕ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (hB : ∀ k x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value (B k) x = 0)
    (hhalf : ∀ k, 2 * ((m : ℝ) * m * ‖B k‖) * ‖OAI.Analysis.PDE.Schauder.poissonHolderOperator hm hα hα1 R‖ ≤ 1 / 2)
    (hPD : ∀ k x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B k) x).PosDef)
    {N K N₀ N₁ : ℝ} (hBN : ∀ k, ‖B k‖ ≤ N) (hFK : ∀ k, ‖F k‖ ≤ K)
    (hUN : ∀ k, ‖U k‖ ≤ N₀) (hVN : ∀ k, ‖V k‖ ≤ N₁)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R)
    (heq : ∀ k x, x ∈ Function.support χ →
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B k) y) (u k) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F k) x)
    (w : EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (w x))) :
    ContDiff ℝ 2 (fun x => χ x * w x) := by
  obtain ⟨C, hC, hc⟩ := OAI.Analysis.PDE.Schauder.uniform_cutoff_schauder hm hα hα1 χ hχ hχc hχR
  have hex (k : ℕ) := hc (B k) (hB k) (hhalf k) (hPD k)
    (u k) (hu k) (F k) (U k) (V k) (hU k) (hV k) (heq k)
  choose W hW hnorm using hex
  let M := C * (|K| + (1 + |N|) * (|N₀| + |N₁|))
  have hb (k) : ‖W k‖ ≤ M := by
    apply (hnorm k).trans
    dsimp only [M]
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply add_le_add ((hFK k).trans (le_abs_self K))
    apply mul_le_mul
    · exact add_le_add le_rfl ((hBN k).trans (le_abs_self N))
    · exact add_le_add ((hUN k).trans (le_abs_self N₀)) ((hVN k).trans (le_abs_self N₁))
    · positivity
    · positivity
  rw [contDiff_iff_contDiffAt]
  intro x
  have hx : x ∈ interior (closedBall x 1) :=
    mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds x zero_lt_one)
  have hh := OAI.Analysis.PDE.Schauder.globalC2Holder_pointwise_limit hα (isCompact_closedBall x 1)
    (convex_closedBall x 1) W hb (fun y => χ y * w y) (by
      intro y _
      simpa only [hW] using (tendsto_const_nhds.mul (hw y)))
  exact (hh.1 x hx).contDiffAt (isOpen_interior.mem_nhds hx)

end OAI.Analysis.PDE.Nonlinear
