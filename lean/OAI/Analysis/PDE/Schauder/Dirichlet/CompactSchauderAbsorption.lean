import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Compact
import OAI.Analysis.Normed.Function.Holder.Banach.Norm

open Set Metric
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

/-- The loss in passing from a fixed local cover to a global Hölder bound
depends on the cover, not on the function or its local bound. -/
theorem compact_fixed_cover_holder_constant
    {X E : Type*} [MetricSpace X] [CompactSpace X] [NormedAddCommGroup E]
    (r : X → ℝ) (hr : ∀ x, 0 < r x) {α : ℝ} (hα : 0 < α) :
    ∃ C > 0, ∀ (f : X → E) M, 0 ≤ M →
      (∀ x y, dist y x ≤ r x → ‖f y‖ ≤ M ∧
        ∀ z, dist z x ≤ r x → ‖f y-f z‖ ≤ M * dist y z ^ α) →
      (∀ x, ‖f x‖ ≤ C * M) ∧
      (∀ x y, ‖f x-f y‖ ≤ C * M * dist x y ^ α) := by
  let P := {p : (X → E) × ℝ // 0 ≤ p.2 ∧
    ∀ x y, dist y x ≤ r x → ‖p.1 y‖ ≤ p.2 ∧
      ∀ z, dist z x ≤ r x → ‖p.1 y-p.1 z‖ ≤ p.2 * dist y z ^ α}
  have hloc : ∀ x ∈ (univ : Set X), ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      ∀ (p : P) y, y ∈ (univ : Set X) → dist y x ≤ ρ →
        ‖p.val.1 y‖ ≤ C * p.val.2 ∧
        ∀ z, z ∈ (univ : Set X) → dist z x ≤ ρ →
          ‖p.val.1 y-p.val.1 z‖ ≤ C * p.val.2 * dist y z ^ α := by
    intro x _
    refine ⟨r x, 1, hr x, zero_lt_one, ?_⟩
    intro p y _ hy
    obtain ⟨hn, hh⟩ := p.property.2 x y hy
    refine ⟨by simpa only [one_mul] using hn, ?_⟩
    intro z _ hz
    simpa only [one_mul] using hh z hz
  obtain ⟨C, hC, hn, hh⟩ := OAI.Analysis.PDE.Elliptic.compact_family_fixed_holder_of_local
    (isCompact_univ : IsCompact (univ : Set X))
    (fun p : P => p.val.1) (fun p : P => p.val.2)
    (fun p => p.property.1) hα hloc
  refine ⟨C, hC, ?_⟩
  intro f M hM hlocal
  let p : P := ⟨(f, M), hM, hlocal⟩
  exact ⟨fun x => hn p x (mem_univ x),
    fun x y => hh p x (mem_univ x) y (mem_univ y)⟩

/-- Absorb infinitesimal local errors into the actual global Hölder norm.
The cover is fixed before choosing the interpolation parameter. -/
theorem compact_holder_norm_absorption
    {X E I : Type*} [MetricSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : X → ℝ) (hr : ∀ x, 0 < r x) {α : ℝ} (hα : 0 < α)
    (u : I → OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (N : I → ℝ) (hN : ∀ i, 0 ≤ N i)
    (hlocal : ∀ ε > 0, ∃ D > 0, ∀ i x y, dist y x ≤ r x →
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value (u i) y‖ ≤ ε * ‖u i‖ + D * N i ∧
      ∀ z, dist z x ≤ r x →
        ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value (u i) y-OAI.Analysis.Normed.Function.Holder.HolderMap.value (u i) z‖ ≤
          (ε * ‖u i‖ + D * N i) * dist y z ^ α) :
    ∃ C > 0, ∀ i, ‖u i‖ ≤ C * N i := by
  obtain ⟨K, hK, hcover⟩ := compact_fixed_cover_holder_constant (E := E) r hr hα
  obtain ⟨D, hD, hloc⟩ := hlocal (1 / (2*K)) (by positivity)
  refine ⟨2*K*D, by positivity, ?_⟩
  intro i
  have hNi := hN i
  have hbudget : 0 ≤ (1 / (2*K)) * ‖u i‖ + D * N i := by positivity
  obtain ⟨hn, hh⟩ := hcover (OAI.Analysis.Normed.Function.Holder.HolderMap.value (u i))
    ((1 / (2*K)) * ‖u i‖ + D * N i) hbudget (hloc i)
  have hu := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα.le
    (mul_nonneg hK.le hbudget) (u i) hn hh
  have hid : K * ((1 / (2*K)) * ‖u i‖ + D * N i) =
      ‖u i‖ / 2 + K*D*N i := by field_simp
  rw [hid] at hu
  nlinarith only [hu]

end OAI.Analysis.PDE.Schauder
