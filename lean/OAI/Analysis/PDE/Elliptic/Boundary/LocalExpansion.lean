import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension
import OAI.Analysis.PDE.Elliptic.Boundary.CenteredHolder

/-! Local form of the boundary first-order expansion. Only smoothness near
the closed half-ball is needed, and the equation is only used inside it. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

theorem boundary_centered_expansion_local
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ m M K : ℝ, m ≤ M → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ),
      (∀ x ∈ closedHalfBall v, ContDiffAt ℝ 2 u x) →
      (∀ x ∈ closedHalfBall v, m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall v, |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∀ z, ‖z‖ ≤ 1 / 4 → inner ℝ v z = 0 →
      ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, ‖x - z‖ ≤ r / 2 → 0 ≤ inner ℝ v x →
        |u x - (fderiv ℝ u z v) * inner ℝ v x| ≤ C * r ^ α * inner ℝ v x := by
  obtain ⟨α, hα, hα1, hbound⟩ := boundary_centered_first_order_holder (ι := ι) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro m M K hm hK
  obtain ⟨C, hC, hbound⟩ := hbound m M K hm hK
  refine ⟨C, hC, ?_⟩
  intro v hv A u hu hb hlo hhi hLu z hz hzv r hr hr1 x hx hxv
  have hc : IsCompact (closedHalfBall v) := by
    have he : closedHalfBall v = Metric.closedBall 0 1 ∩ {x | 0 ≤ inner ℝ v x} := by
      ext x
      simp [closedHalfBall, Metric.mem_closedBall, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall 0 1).inter_right
      (isClosed_le continuous_const (continuous_const.inner continuous_id))
  obtain ⟨g, hg, hgu⟩ := exists_contDiff_extension_near_compact hc hu
  have hzmem : z ∈ closedHalfBall v := ⟨by linarith, by simp [hzv]⟩
  have hxmem : x ∈ closedHalfBall v := by
    refine ⟨?_, hxv⟩
    have hh := norm_add_le (x - z) z
    rw [sub_add_cancel] at hh
    linarith
  have hh := hbound v hv A g hg (fun y hy => by
    rw [(hgu y hy).eq_of_nhds]; exact hb y hy) hlo hhi
    (fun y hy => by
      rw [ellipticTrace_congr_germ A (hgu y ⟨hy.1.le, hy.2.le⟩)]
      exact hLu y hy) z hz hzv r hr hr1 x hx hxv
  rwa [(hgu x hxmem).eq_of_nhds, (hgu z hzmem).fderiv_eq (𝕜 := ℝ)] at hh

end OAI.Analysis.PDE.Elliptic
