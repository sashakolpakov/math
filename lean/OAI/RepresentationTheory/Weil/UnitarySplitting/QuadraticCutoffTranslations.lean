import OAI.RepresentationTheory.Weil.UnitarySplitting.ProperQuadratic
import OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterCutoffs

/-! # Quadratic Cutoff Translations -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticCutoffTranslations.Construction

noncomputable section

/-! Sublevel cutoffs of an anisotropic quadratic form are preserved by
bounded translations once the cutoff is large enough. -/

open _root_.MeasureTheory _root_.Topology

theorem quadratic_bound_implies_linear_bound
    {c L r x : ℝ} (hc : 0 < c) (hr : L ^ 2 / c ≤ r)
    (hx : c * x ^ 2 ≤ r) : L * x ≤ r := by
  have hLsq : L ^ 2 ≤ r * c := (div_le_iff₀ hc).mp hr
  have hxsq := mul_le_mul_of_nonneg_left hx hc.le
  nlinarith [sq_nonneg (c * x - L)]

theorem anisotropic_quadratic_cutoff_translation
    {F V : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [NormedAddCommGroup V] [NormedSpace F V] [ProperSpace V]
    (q : V → F) (hq : Continuous q) (B : V →L[F] V →L[F] F)
    (hadd : ∀ v x, q (v + x) = q v + q x + B v x)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ x, c * ‖x‖ ^ 2 ≤ ‖q x‖)
    (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∀ v : V, ‖v‖ ≤ M → ∀ x : V,
      q (v + x) ∈ Metric.closedBall 0 r ↔ q x ∈ Metric.closedBall 0 r := by
  obtain ⟨Q, hQpos, hQ⟩ := ((isCompact_closedBall (0 : V) M).image hq).isBounded.exists_pos_norm_le
  let L := ‖B‖ * M
  let R := max Q (L ^ 2 / c)
  have hR : 0 < R := hQpos.trans_le (le_max_left _ _)
  have hforward (r : ℝ) (hr : R ≤ r) (v : V) (hv : ‖v‖ ≤ M)
      (x : V) (hx : ‖q x‖ ≤ r) : ‖q (v + x)‖ ≤ r := by
    have hqv : ‖q v‖ ≤ r := (hQ (q v) ⟨v, by simpa using hv, rfl⟩).trans
      ((le_max_left _ _).trans hr)
    have hB : ‖B v x‖ ≤ r := calc
      ‖B v x‖ ≤ ‖B‖ * ‖v‖ * ‖x‖ := B.le_opNorm₂ v x
      _ ≤ L * ‖x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv (norm_nonneg B)) (norm_nonneg x)
      _ ≤ r := quadratic_bound_implies_linear_bound hc
        ((le_max_right _ _).trans hr) ((hlow x).trans hx)
    rw [hadd]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hqv hx)) hB)
  refine ⟨R, hR, fun r hr v hv x => ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    have hh := hforward r hr (-v) (by simpa using hv) (v + x) hx
    simpa only [neg_add_cancel_left] using hh
  · exact hforward r hr v hv x

theorem quadratic_cutoff_complete_square
    {F V : Type} [Field F] [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant]
    (ψ : AddChar F ℂ) (q : V → F) (B : V → V → F)
    (hadd : ∀ v x, q (v + x) = q v + q x + B v x)
    (D : Set V) (v : V) (hD : ∀ x, v + x ∈ D ↔ x ∈ D) :
    (∫ x, D.indicator (fun x => ψ (q x + B v x)) x ∂μ) =
      ψ (-q v) * ∫ x, D.indicator (fun x => ψ (q x)) x ∂μ := by
  classical
  have heq (x : V) : D.indicator (fun x => ψ (q x)) (v + x) =
      ψ (q v) * D.indicator (fun x => ψ (q x + B v x)) x := by
    by_cases hx : x ∈ D
    · rw [Set.indicator_of_mem ((hD x).mpr hx), Set.indicator_of_mem hx,
        hadd, add_assoc, ψ.map_add_eq_mul]
    · rw [Set.indicator_of_notMem (fun h => hx ((hD x).mp h)),
        Set.indicator_of_notMem hx, mul_zero]
  have hh := integral_add_left_eq_self (μ := μ) (D.indicator (fun x => ψ (q x))) v
  simp_rw [heq, integral_const_mul] at hh
  rw [← hh, ← mul_assoc, ← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one, one_mul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticCutoffTranslations.Construction
