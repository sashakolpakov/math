import Mathlib

/-! Quantitative compact-cover globalization preserving the original
Hölder exponent and the linear dependence on the data norm. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem compact_family_fixed_holder_of_local
    {X E P : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    {K : Set X} (hK : IsCompact K) (F : P → X → E)
    (N : P → ℝ) (hN : ∀ p, 0 ≤ N p) {α : ℝ} (hα : 0 < α)
    (hlocal : ∀ x ∈ K, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ p y, y ∈ K → dist y x ≤ r →
        ‖F p y‖ ≤ C * N p ∧
        ∀ z, z ∈ K → dist z x ≤ r →
          ‖F p y - F p z‖ ≤ C * N p * dist y z ^ α) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p x, x ∈ K → ‖F p x‖ ≤ C * N p) ∧
      (∀ p x, x ∈ K → ∀ y, y ∈ K → ‖F p x - F p y‖ ≤ C * N p * dist x y ^ α) := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · subst K
    exact ⟨1, zero_lt_one, by simp, by simp⟩
  choose r C hr hC hloc using fun x : K => hlocal x x.property
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : X) (r x / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using half_pos (hr ⟨x, hx⟩)⟩)
  have htn : t.Nonempty := by
    obtain ⟨x, hx⟩ := hKn
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨i, hi⟩
  let δ := t.inf' htn (fun i => r i / 2)
  let C₀ := t.sup' htn C
  have hδ : 0 < δ := (Finset.lt_inf'_iff htn).2 (fun i _ => half_pos (hr i))
  have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ _
  have hC₀ : 0 < C₀ := by
    obtain ⟨i, hi⟩ := htn
    exact lt_of_lt_of_le (hC i) (Finset.le_sup' C hi)
  have hnorm : ∀ p y, y ∈ K → ‖F p y‖ ≤ C₀ * N p := by
    intro p y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht hy)
    have hyi' : dist y (i : X) < r i / 2 := hyi
    exact (hloc i p y hy (by linarith [hr i])).1.trans
      (mul_le_mul_of_nonneg_right (Finset.le_sup' C hi) (hN p))
  let D := C₀ + 2 * C₀ / δ ^ α + 1
  have hterm : 0 ≤ 2 * C₀ / δ ^ α := by positivity
  have hCD : C₀ ≤ D := by dsimp [D]; linarith
  have hDD : 2 * C₀ / δ ^ α ≤ D := by dsimp [D]; linarith
  refine ⟨D, by dsimp [D]; positivity, ?_, ?_⟩
  · intro p x hx
    exact (hnorm p x hx).trans (mul_le_mul_of_nonneg_right hCD (hN p))
  · intro p x hx y hy
    by_cases hclose : dist x y < δ
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
      have hδi : δ ≤ r i / 2 := Finset.inf'_le _ hi
      have hxi' : dist x (i : X) < r i / 2 := hxi
      have hyi : dist y (i : X) ≤ r i := by
        have ht' := dist_triangle y x (i : X)
        rw [dist_comm y x] at ht'
        linarith
      have hh := (hloc i p x hx (by linarith)).2 y hy hyi
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((Finset.le_sup' C hi).trans hCD) (hN p))
          (Real.rpow_nonneg dist_nonneg _))
    · have hfar : δ ≤ dist x y := le_of_not_gt hclose
      have hp : δ ^ α ≤ dist x y ^ α := Real.rpow_le_rpow hδ.le hfar hα.le
      calc
        ‖F p x - F p y‖ ≤ ‖F p x‖ + ‖F p y‖ := norm_sub_le _ _
        _ ≤ 2 * C₀ * N p := by linarith [hnorm p x hx, hnorm p y hy]
        _ = (2 * C₀ / δ ^ α) * N p * δ ^ α := by field_simp
        _ ≤ (2 * C₀ / δ ^ α) * N p * dist x y ^ α :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hterm (hN p))
        _ ≤ D * N p * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD (hN p))
            (Real.rpow_nonneg dist_nonneg _)

theorem compact_family_fixed_holder_of_open_local
    {X E P : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    {K : Set X} (hK : IsCompact K) (F : P → X → E)
    (N : P → ℝ) (hN : ∀ p, 0 ≤ N p) {α : ℝ} (hα : 0 < α)
    (hlocal : ∀ x ∈ K, ∃ (U : Set X) (C : ℝ),
      IsOpen U ∧ x ∈ U ∧ 0 < C ∧
      (∀ p y, y ∈ K ∩ U → ‖F p y‖ ≤ C * N p) ∧
      (∀ p y, y ∈ K ∩ U → ∀ z, z ∈ K ∩ U →
        ‖F p y - F p z‖ ≤ C * N p * dist y z ^ α)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p x, x ∈ K → ‖F p x‖ ≤ C * N p) ∧
      (∀ p x, x ∈ K → ∀ y, y ∈ K → ‖F p x - F p y‖ ≤ C * N p * dist x y ^ α) := by
  apply compact_family_fixed_holder_of_local hK F N hN hα
  intro x hx
  obtain ⟨U, C, hU, hxU, hC, hn, hh⟩ := hlocal x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hxU
  refine ⟨r/2, C, half_pos hr, hC, ?_⟩
  intro p y hy hyd
  have hyU : y ∈ U := hrU (show y ∈ ball x r by change dist y x < r; linarith)
  refine ⟨hn p y ⟨hy, hyU⟩, ?_⟩
  intro z hz hzd
  exact hh p y ⟨hy, hyU⟩ z ⟨hz, hrU (show z ∈ ball x r by change dist z x < r; linarith)⟩

end OAI.Analysis.PDE.Elliptic
