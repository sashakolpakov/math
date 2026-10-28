import OAI.Analysis.PDE.Weak.Elliptic.WeakCompactness

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Weak

/-- Bounded sequences in an actual closed Hilbert subspace have a limit
in that same subspace preserving every convergent linear pairing. -/
theorem exists_weak_limit_in_submodule {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Submodule ℝ H) (hS : IsClosed (S : Set H))
    (u : ℕ → H) (hu : ∀ n, u n ∈ S) {C : ℝ} (hC : ∀ n, ‖u n‖ ≤ C) :
    ∃ g : H, g ∈ S ∧ ‖g‖ ≤ C ∧ ∀ (φ : H →L[ℝ] ℝ) (l : ℝ),
      Tendsto (fun n ↦ φ (u n)) atTop (𝓝 l) → φ g = l := by
  let : CompleteSpace S := hS.completeSpace_coe
  let us : ℕ → S := fun n ↦ ⟨u n, hu n⟩
  obtain ⟨gs, hgs, hlimit⟩ := exists_weak_limit_preserving_scalar_limits us hC
  refine ⟨gs, gs.property, hgs, ?_⟩
  intro φ l hl
  let φs : S →L[ℝ] ℝ := φ.comp S.subtypeL
  let v : S := (toDual ℝ S).symm φs
  have hv (w : S) : inner ℝ w v = φs w := by
    rw [real_inner_comm]
    change toDual ℝ S v w = φs w
    simp [v]
  have he := hlimit v l (by simpa [hv, φs, us] using hl)
  simpa [hv, φs] using he

end OAI.Analysis.PDE.Weak
