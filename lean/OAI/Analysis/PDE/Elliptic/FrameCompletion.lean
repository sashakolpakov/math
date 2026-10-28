import OAI.Analysis.PDE.Elliptic.RankOneFrame

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

/-- If each frame has the same sum, a uniformly positive representation in
one frame extends to a uniformly positive representation in all frames.
The new lower bound is chosen before the active frame and its coefficients. -/
theorem finite_frame_positive_completion
    {B J V : Type*} [Fintype B] [Nonempty B] [Fintype J]
    [AddCommGroup V] [Module ℝ V]
    (v : B → J → V) (P : V) (hframe : ∀ b, ∑ j, v b j = P)
    {m M : ℝ} (hm : 0 < m) (hM : m ≤ M) :
    ∃ δ > 0, ∀ b₀ : B, ∀ a : J → ℝ,
      (∀ j, m ≤ a j ∧ a j ≤ M) →
      ∃ c : B → J → ℝ,
        (∀ b j, δ ≤ c b j ∧ c b j ≤ M) ∧
        (∑ b, ∑ j, c b j • v b j) = ∑ j, a j • v b₀ j := by
  classical
  let N : ℝ := Fintype.card B
  have hN : 1 ≤ N := by
    have hn : 1 ≤ Fintype.card B := Fintype.card_pos
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let δ := m / (2 * N)
  have hδ : 0 < δ := div_pos hm (by positivity)
  have hδeq : δ * (2 * N) = m := div_mul_cancel₀ _ (by positivity)
  have hδN : δ ≤ δ * N := by nlinarith
  refine ⟨δ, hδ, ?_⟩
  intro b₀ a ha
  let c : B → J → ℝ := fun b j ↦ δ + if b = b₀ then a j - δ * N else 0
  refine ⟨c, ?_, ?_⟩
  · intro b j
    by_cases hb : b = b₀
    · simp only [c, hb, ite_true]
      constructor <;> nlinarith [(ha j).1, (ha j).2]
    · simp only [c, hb, ite_false, add_zero]
      exact ⟨le_rfl, by nlinarith⟩
  · have hs (b : B) : (∑ j, c b j • v b j) =
        δ • P + if b = b₀ then (∑ j, a j • v b₀ j) - (δ * N) • P else 0 := by
      by_cases hb : b = b₀
      · subst b
        simp only [c, ite_true, add_smul, sub_smul, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.smul_sum, hframe]
      · simp only [c, hb, ite_false, add_zero, ← Finset.smul_sum, hframe]
    simp_rw [hs]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Nat.cast_smul_eq_nsmul ℝ]
    change N • (δ • P) + ((∑ j, a j • v b₀ j) - (δ * N) • P) = _
    module

end OAI.Analysis.PDE.Elliptic
