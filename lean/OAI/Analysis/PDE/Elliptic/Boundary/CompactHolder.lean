import Mathlib

/-! Uniform local Hölder estimates on a compact set imply a uniform global
Hölder estimate.  The local radii and exponents may vary with the center,
but not with the member of the bounded family. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem compact_family_holder_of_local
    {X V P : Type*} [PseudoMetricSpace X] [NormedAddCommGroup V]
    {K : Set X} (hK : IsCompact K) (F : P → X → V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ p x, x ∈ K → ‖F p x‖ ≤ M)
    (hlocal : ∀ x ∈ K, ∃ r a C : ℝ,
      0 < r ∧ 0 < a ∧ a < 1 ∧ 0 < C ∧
      ∀ p y, y ∈ K → dist y x ≤ r → ∀ z, z ∈ K → dist z x ≤ r →
        ‖F p y - F p z‖ ≤ C * dist y z ^ a) :
    ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 < C ∧
      ∀ p y, y ∈ K → ∀ z, z ∈ K → ‖F p y - F p z‖ ≤ C * dist y z ^ a := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · subst K
    exact ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, by simp⟩
  choose r a C hr ha ha1 hC hloc using fun x : K => hlocal x x.property
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : X) (r x / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using half_pos (hr ⟨x, hx⟩)⟩)
  have htn : t.Nonempty := by
    obtain ⟨x, hx⟩ := hKn
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨i, hi⟩
  let α := min (1 / 2 : ℝ) (t.inf' htn a)
  let δ := min (1 : ℝ) (t.inf' htn (fun i => r i / 2))
  let C₀ := t.sup' htn C
  have hα : 0 < α := lt_min (by norm_num) ((Finset.lt_inf'_iff htn).2 (fun i _ => ha i))
  have hα1 : α < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδ : 0 < δ := lt_min zero_lt_one ((Finset.lt_inf'_iff htn).2 (fun i _ => half_pos (hr i)))
  have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ _
  have hC₀ : 0 < C₀ := by
    obtain ⟨i, hi⟩ := htn
    exact lt_of_lt_of_le (hC i) (Finset.le_sup' C hi)
  have hterm : 0 ≤ 2 * M / δ ^ α := div_nonneg (by positivity) hδα.le
  refine ⟨α, C₀ + 2 * M / δ ^ α + 1, hα, hα1, by positivity, ?_⟩
  intro p y hy z hz
  have hdist : 0 ≤ dist y z := dist_nonneg
  by_cases hclose : dist y z < δ
  · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht hy)
    have hδi : δ ≤ r i / 2 := (min_le_right _ _).trans (Finset.inf'_le _ hi)
    have hyi' : dist y (i : X) < r i / 2 := hyi
    have hzi : dist z (i : X) ≤ r i := by
      have ht' := dist_triangle z y (i : X)
      rw [dist_comm z y] at ht'
      linarith
    have hh := hloc i p y hy (by linarith) z hz hzi
    have hαi : α ≤ a i := (min_le_right _ _).trans (Finset.inf'_le _ hi)
    have hd1 : dist y z ≤ 1 := hclose.le.trans (min_le_left _ _)
    have hp : dist y z ^ a i ≤ dist y z ^ α := by
      exact Real.rpow_le_rpow_of_exponent_ge' hdist hd1 hα.le hαi
    calc
      ‖F p y - F p z‖ ≤ C i * dist y z ^ a i := hh
      _ ≤ C₀ * dist y z ^ α := mul_le_mul (Finset.le_sup' C hi) hp
        (Real.rpow_nonneg hdist _) hC₀.le
      _ ≤ (C₀ + 2 * M / δ ^ α + 1) * dist y z ^ α := by
        gcongr
        linarith
  · have hfar : δ ≤ dist y z := le_of_not_gt hclose
    have hp : δ ^ α ≤ dist y z ^ α := Real.rpow_le_rpow hδ.le hfar hα.le
    calc
      ‖F p y - F p z‖ ≤ ‖F p y‖ + ‖F p z‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hbound p y hy, hbound p z hz]
      _ = (2 * M / δ ^ α) * δ ^ α := by field_simp
      _ ≤ (2 * M / δ ^ α) * dist y z ^ α := mul_le_mul_of_nonneg_left hp hterm
      _ ≤ (C₀ + 2 * M / δ ^ α + 1) * dist y z ^ α := by
        gcongr
        linarith

end OAI.Analysis.PDE.Elliptic
