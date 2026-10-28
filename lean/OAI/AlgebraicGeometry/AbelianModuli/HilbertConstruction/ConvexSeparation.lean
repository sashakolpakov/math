import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Convex Separation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConvexSeparation

noncomputable section

/-! HilbertConstruction-local separation results, adapted from Mathlib's geometric
Hahn–Banach proof and using the default elaboration settings. -/
open Set
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E]

private theorem separateConvexOpenSet {s : Set E} (hs₀ : (0 : E) ∈ s)
    (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) :
    ∃ f : StrongDual ℝ E, f x₀ = 1 ∧ ∀ x ∈ s, f x < 1 := by
  let f : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  have := exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) ?_
  · obtain ⟨φ, hφ₁, hφ₂⟩ := this
    have hφ₃ : φ x₀ = 1 := by
      rw [← f.domain.coe_mk x₀ (Submodule.mem_span_singleton_self _), hφ₁,
        LinearPMap.mkSpanSingleton'_apply_self]
    have hφ₄ : ∀ x ∈ s, φ x < 1 := fun x hx =>
      (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_isOpen hs₂ hx)
    refine ⟨⟨φ, ?_⟩, hφ₃, hφ₄⟩
    refine φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (Nonempty.vadd_set ⟨0, hs₀⟩)
      (vadd_set_subset_iff.mpr fun x hx => ?_)
    change φ (-x₀ + x) ≠ 0
    rw [map_add, map_neg]
    specialize hφ₄ x hx
    linarith
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearPMap.mkSpanSingleton'_apply]
  simp only [mul_one, smul_eq_mul]
  obtain h | h := le_or_gt y 0
  · exact h.trans (gauge_nonneg _)
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, RingHom.id_apply, le_mul_iff_one_le_right h]
    exact one_le_gauge_of_notMem (hs₁.starConvex hs₀)
      (absorbent_nhds_zero <| hs₂.mem_nhds hs₀).absorbs hx₀

private theorem separateConvexOpenPoint {s : Set E} {x : E}
    (hs : Convex ℝ s) (hopen : IsOpen s) (hne : s.Nonempty) (hx : x ∉ s) :
    ∃ f : StrongDual ℝ E, ∀ a ∈ s, f a < f x := by
  obtain ⟨a₀, ha₀⟩ := hne
  let C := (-a₀) +ᵥ s
  have hC0 : (0 : E) ∈ C := by
    exact ⟨a₀, ha₀, neg_add_cancel a₀⟩
  have hxC : x - a₀ ∉ C := by
    rintro ⟨a, ha, he⟩
    have hax : a = x := by
      change -a₀ + a = x - a₀ at he
      apply add_left_cancel (a := -a₀)
      simpa only [sub_eq_add_neg, add_comm] using he
    exact hx (hax ▸ ha)
  obtain ⟨f, hf, hsep⟩ := separateConvexOpenSet hC0 (hs.vadd (-a₀))
    (hopen.vadd (-a₀)) hxC
  refine ⟨f, fun a ha => ?_⟩
  have h := hsep (-a₀ + a) ⟨a, ha, rfl⟩
  rw [map_add, map_neg] at h
  rw [map_sub] at hf
  linarith

theorem separateConvexSetAtExteriorPoint {s : Set E} {x : E}
    (hs : Convex ℝ s) (hx : x ∉ interior s) (hint : (interior s).Nonempty) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ a ∈ s, f a ≤ f x := by
  obtain ⟨f, hsep⟩ := separateConvexOpenPoint hs.interior isOpen_interior hint hx
  refine ⟨f, ?_, fun a ha => ?_⟩
  · obtain ⟨b, hb⟩ := hint
    intro hz
    have h := hsep b hb
    simp [hz] at h
  · apply closure_minimal (fun b hb => (hsep b hb).le)
      (isClosed_Iic.preimage f.continuous)
    simpa only [hs.closure_interior_eq_closure_of_nonempty_interior hint] using subset_closure ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConvexSeparation
