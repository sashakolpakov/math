import OAI.Analysis.Normed.Function.Holder.Banach.Composition
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Uniform a priori bounds from actual operator-norm compactness.
This elementary lemma does not assume uniform inverse bounds. -/
open Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_lower_bound_of_subsequence_lower_bound
    (A : I → E →L[ℝ] F)
    (hcompact : ∀ i : ℕ → I, ∃ (φ : ℕ → ℕ) (L : E →L[ℝ] F) (C : ℝ),
      StrictMono φ ∧ 0 ≤ C ∧ (∀ x, ‖x‖ ≤ C * ‖L x‖) ∧
        Tendsto (fun k => A (i (φ k))) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x, ‖x‖ ≤ C * ‖A i x‖ := by
  by_contra! h
  have hw (k : ℕ) : ∃ i x, ((k : ℝ) + 1) * ‖A i x‖ < ‖x‖ :=
    h ((k : ℝ) + 1) (by positivity)
  choose i x hx using hw
  obtain ⟨φ,L,C,hφ,hC,hlowerC,hlim⟩ := hcompact i
  let B : ℝ := C + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hLB : C ≤ B := by dsimp [B]; linarith
  have he : Tendsto (fun k => ‖L - A (i (φ k))‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => L)
      atTop (𝓝 L)).sub hlim).norm
  have hevent : ∀ᶠ k in atTop,
      ‖L - A (i (φ k))‖ < (2 * B)⁻¹ :=
    (tendsto_order.1 he).2 _ (by positivity)
  have hn : Tendsto (fun k => (φ k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hnevent : ∀ᶠ k in atTop, 2 * B ≤ (φ k : ℝ) + 1 :=
    (hn.eventually (eventually_ge_atTop (2 * B))).mono (fun k hk => by linarith)
  obtain ⟨k,hk,hkn⟩ := (hevent.and hnevent).exists
  let y := x (φ k)
  have hy : 0 < ‖y‖ := lt_of_le_of_lt (by positivity) (hx (φ k))
  have hAy : ‖A (i (φ k)) y‖ < (2 * B)⁻¹ * ‖y‖ := by
    have hh := hx (φ k)
    have hm := mul_le_mul_of_nonneg_right hkn (norm_nonneg (A (i (φ k)) y))
    have hsmall := mul_lt_mul_of_pos_left (hm.trans_lt hh)
      (show 0 < (2 * B)⁻¹ by positivity)
    simpa only [← mul_assoc, inv_mul_cancel₀ (show 2 * B ≠ 0 by positivity), one_mul] using hsmall
  have hLy : ‖L y‖ < B⁻¹ * ‖y‖ := by
    calc
      ‖L y‖ ≤ ‖(L - A (i (φ k))) y‖ + ‖A (i (φ k)) y‖ := by
        simpa using norm_add_le ((L - A (i (φ k))) y)
          (A (i (φ k)) y)
      _ ≤ ‖L - A (i (φ k))‖ * ‖y‖ + ‖A (i (φ k)) y‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ y) le_rfl
      _ < (2 * B)⁻¹ * ‖y‖ + (2 * B)⁻¹ * ‖y‖ :=
        add_lt_add (mul_lt_mul_of_pos_right hk hy) hAy
      _ = B⁻¹ * ‖y‖ := by field_simp; ring
  have hlower : ‖y‖ ≤ B * ‖L y‖ := by
    exact (hlowerC y).trans (mul_le_mul_of_nonneg_right hLB (norm_nonneg _))
  have hsmall := mul_lt_mul_of_pos_left hLy hB
  have hi : B * (B⁻¹ * ‖y‖) = ‖y‖ := by
    rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
  rw [hi] at hsmall
  exact (not_lt_of_ge hlower) hsmall

theorem uniform_lower_bound_of_subsequence_equiv
    (A : I → E →L[ℝ] F)
    (hcompact : ∀ i : ℕ → I, ∃ (φ : ℕ → ℕ) (L : E ≃L[ℝ] F),
      StrictMono φ ∧ Tendsto (fun k => A (i (φ k))) atTop (𝓝 L.toContinuousLinearMap)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x, ‖x‖ ≤ C * ‖A i x‖ := by
  apply uniform_lower_bound_of_subsequence_lower_bound A
  intro i
  obtain ⟨φ,L,hφ,hlim⟩ := hcompact i
  refine ⟨φ,L.toContinuousLinearMap,‖L.symm.toContinuousLinearMap‖,hφ,norm_nonneg _,?_,hlim⟩
  intro x
  change ‖x‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L x‖
  have h := L.symm.toContinuousLinearMap.le_opNorm (L x)
  change ‖L.symm (L x)‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L x‖ at h
  simpa only [L.symm_apply_apply] using h

end OAI.Analysis.PDE.Dirichlet
