import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Quadratic Norm At -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormAt.Construction

noncomputable section

section

/-! Topological facts about the quadratic norm x² + y² needed for the nonsplit local case. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

theorem sum_two_squares_ne_zero {k : Type*} [Field k]
    (h : ¬ ∃ r : k, r ^ 2 = -1) {x y : k} (hxy : x ≠ 0 ∨ y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  intro he
  by_cases hy : y = 0
  · have hx : x = 0 := by simpa [hy] using he
    exact hxy.elim (fun hn => hn hx) (fun hn => hn hy)
  · apply h
    refine ⟨x / y, ?_⟩
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hy)]
    linear_combination he

theorem one_add_sq_norm_lower_bound
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ r : k, r ^ 2 = -1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : k, ‖t‖ ≤ 1 → c ≤ ‖1 + t ^ 2‖ := by
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hnd
  have hc : Continuous (fun t : k => ‖1 + t ^ 2‖) := by fun_prop
  obtain ⟨t, _, ht⟩ := (isCompact_closedBall (0 : k) 1).exists_isMinOn
    ⟨0, by simp⟩ hc.continuousOn
  refine ⟨‖1 + t ^ 2‖, norm_pos_iff.mpr ?_, fun u hu => ht (by simpa using hu)⟩
  intro he
  exact h ⟨t, by linear_combination he⟩

theorem sum_two_squares_norm_lower_bound
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ r : k, r ^ 2 = -1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : k, c * max ‖x‖ ‖y‖ ^ 2 ≤ ‖x ^ 2 + y ^ 2‖ := by
  obtain ⟨c, hc, hb⟩ := one_add_sq_norm_lower_bound hnd h
  refine ⟨c, hc, ?_⟩
  have hbound (x y : k) (hxy : ‖y‖ ≤ ‖x‖) : c * ‖x‖ ^ 2 ≤ ‖x ^ 2 + y ^ 2‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have ht : ‖y / x‖ ≤ 1 := by rw [norm_div, div_le_one hx0]; exact hxy
    have hid : x ^ 2 + y ^ 2 = x ^ 2 * (1 + (y / x) ^ 2) := by field_simp
    rw [hid, norm_mul, norm_pow]
    nlinarith [hb (y / x) ht, sq_nonneg ‖x‖]
  intro x y
  rcases le_total ‖y‖ ‖x‖ with hxy | hxy
  · simpa only [max_eq_left hxy] using hbound x y hxy
  · simpa only [max_eq_right hxy, add_comm] using hbound y x hxy

theorem quadraticNorm_one_isCompact
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ r : k, r ^ 2 = -1) :
    IsCompact {p : k × k | p.1 ^ 2 + p.2 ^ 2 = 1} := by
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hnd
  obtain ⟨c, hc, hb⟩ := sum_two_squares_norm_lower_bound hnd h
  have hclosed : IsClosed {p : k × k | p.1 ^ 2 + p.2 ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : k × k) (Real.sqrt c⁻¹)).of_isClosed_subset hclosed
  intro p hp
  have hnorm := hb p.1 p.2
  rw [hp, norm_one] at hnorm
  have hs : (max ‖p.1‖ ‖p.2‖) ^ 2 ≤ c⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using hnorm
  have hm : max ‖p.1‖ ‖p.2‖ ≤ Real.sqrt c⁻¹ :=
    (Real.le_sqrt (le_trans (norm_nonneg _) (le_max_left _ _)) (inv_nonneg.mpr hc.le)).mpr hs
  simpa only [mem_closedBall, dist_zero_right, Prod.norm_def] using hm

theorem square_range_mem_nhds_one
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] :
    Set.range (fun x : k => x ^ 2) ∈ 𝓝 (1 : k) := by
  have hd : HasStrictDerivAt (fun x : k => x ^ 2) 2 1 := by
    simpa using! (hasStrictDerivAt_id (1 : k)).pow 2
  have he := hd.map_nhds_eq (by norm_num : (2 : k) ≠ 0)
  have hr : Set.range (fun x : k => x ^ 2) ∈
      Filter.map (fun x : k => x ^ 2) (𝓝 (1 : k)) := by
    simp only [Filter.mem_map, Set.preimage_range, Filter.univ_mem]
  simpa only [he, one_pow] using hr

end

section

/-! The compact norm-one group for the quadratic algebra obtained by adjoining a square root of -1. -/

abbrev QuadraticNormOne (k : Type*) [CommRing k] :=
  {p : k × k | p.1 ^ 2 + p.2 ^ 2 = 1}

namespace QuadraticNormOne

variable {k : Type*} [CommRing k]

instance : One (QuadraticNormOne k) := ⟨⟨(1, 0), by simp⟩⟩

instance : Mul (QuadraticNormOne k) where
  mul p q := ⟨(p.val.1 * q.val.1 - p.val.2 * q.val.2,
    p.val.1 * q.val.2 + p.val.2 * q.val.1), by
      change _ = 1
      calc
        _ = (p.val.1 ^ 2 + p.val.2 ^ 2) * (q.val.1 ^ 2 + q.val.2 ^ 2) := by ring
        _ = 1 := by rw [p.property, q.property, mul_one]⟩

instance : Inv (QuadraticNormOne k) := ⟨fun p => ⟨(p.val.1, -p.val.2), by
  change p.val.1 ^ 2 + (-p.val.2) ^ 2 = 1
  rw [neg_sq]
  exact p.property⟩⟩

@[simp] theorem one_val : (1 : QuadraticNormOne k).val = (1, 0) := rfl

@[simp] theorem mul_val (p q : QuadraticNormOne k) :
    (p * q).val = (p.val.1 * q.val.1 - p.val.2 * q.val.2,
      p.val.1 * q.val.2 + p.val.2 * q.val.1) := rfl

@[simp] theorem inv_val (p : QuadraticNormOne k) :
    p⁻¹.val = (p.val.1, -p.val.2) := rfl

instance : CommGroup (QuadraticNormOne k) where
  mul_assoc p q r := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> ring
  one_mul p := by apply Subtype.ext; simp
  mul_one p := by apply Subtype.ext; simp
  inv_mul_cancel p := by
    apply Subtype.ext
    apply Prod.ext
    · change p.val.1 * p.val.1 - (-p.val.2) * p.val.2 = 1
      have hp : p.val.1 ^ 2 + p.val.2 ^ 2 = 1 := p.property
      linear_combination hp
    · change p.val.1 * p.val.2 + (-p.val.2) * p.val.1 = 0
      ring
  mul_comm p q := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> ring

instance [TopologicalSpace k] [IsTopologicalRing k] : IsTopologicalGroup (QuadraticNormOne k) where
  continuous_mul := by
    apply Continuous.subtype_mk
    change Continuous (fun p : QuadraticNormOne k × QuadraticNormOne k =>
      (p.1.val.1 * p.2.val.1 - p.1.val.2 * p.2.val.2,
       p.1.val.1 * p.2.val.2 + p.1.val.2 * p.2.val.1))
    fun_prop
  continuous_inv := by
    apply Continuous.subtype_mk
    change Continuous (fun p : QuadraticNormOne k => (p.val.1, -p.val.2))
    fun_prop

def minusOne : QuadraticNormOne k := ⟨(-1, 0), by simp⟩

@[simp] theorem minusOne_val : (minusOne : QuadraticNormOne k).val = (-1, 0) := rfl

theorem sq_eq_one_iff {k : Type*} [Field k] [CharZero k] (p : QuadraticNormOne k) :
    p ^ 2 = 1 ↔ p = 1 ∨ p = minusOne := by
  constructor
  · intro hp
    rw [pow_two] at hp
    have hx := congrArg (fun q : QuadraticNormOne k => q.val.1) hp
    have hy := congrArg (fun q : QuadraticNormOne k => q.val.2) hp
    change p.val.1 * p.val.1 - p.val.2 * p.val.2 = 1 at hx
    change p.val.1 * p.val.2 + p.val.2 * p.val.1 = 0 at hy
    have hxy : p.val.1 * p.val.2 = 0 := by linear_combination (1 / 2 : k) * hy
    have hy0 : p.val.2 = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · exfalso
        have hn : p.val.1 ^ 2 + p.val.2 ^ 2 = 1 := p.property
        rw [hx0] at hx
        rw [hx0, zero_pow two_ne_zero, zero_add] at hn
        have he : (2 : k) = 0 := by linear_combination -hx - hn
        exact (by norm_num : (2 : k) ≠ 0) he
      · exact hy0
    have hx2 : p.val.1 ^ 2 = 1 := by
      have hn : p.val.1 ^ 2 + p.val.2 ^ 2 = 1 := p.property
      simpa only [hy0, zero_pow two_ne_zero, add_zero] using hn
    rcases _root_.sq_eq_one_iff.mp hx2 with hx1 | hx1
    · left
      apply Subtype.ext
      exact Prod.ext hx1 hy0
    · right
      apply Subtype.ext
      exact Prod.ext hx1 hy0
  · rintro (rfl | rfl)
    · simp
    · apply Subtype.ext
      simp [pow_two, minusOne]

end QuadraticNormOne

theorem quadraticNormOne_compactSpace
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ r : k, r ^ 2 = -1) :
    CompactSpace (QuadraticNormOne k) :=
  isCompact_iff_compactSpace.mp (quadraticNorm_one_isCompact hnd h)

end

/-! Rational coordinates on the nonsplit norm-one group. -/

open Set

variable {k : Type*} [Field k]

theorem one_add_sq_ne_zero (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k) :
    1 + t ^ 2 ≠ 0 := by
  intro he
  exact h ⟨t, by linear_combination he⟩

def quadraticNormChart (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k) : QuadraticNormOne k :=
  ⟨((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)), by
    change _ = 1
    field_simp [one_add_sq_ne_zero h t]
    ring⟩

def quadraticNormCoordinate (p : QuadraticNormOne k) : k := p.val.2 / (1 + p.val.1)

theorem quadraticNormChart_zero (h : ¬ ∃ r : k, r ^ 2 = -1) :
    quadraticNormChart h 0 = 1 := by
  apply Subtype.ext
  simp [quadraticNormChart]

theorem quadraticNormChart_re_add_one [CharZero k]
    (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k) :
    1 + (quadraticNormChart h t).val.1 = 2 / (1 + t ^ 2) := by
  dsimp [quadraticNormChart]
  field_simp [one_add_sq_ne_zero h t]
  ring

theorem quadraticNormChart_ne_minusOne [CharZero k]
    (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k) :
    quadraticNormChart h t ≠ QuadraticNormOne.minusOne := by
  intro he
  have hx := quadraticNormChart_re_add_one h t
  rw [he] at hx
  change 1 + (-1 : k) = 2 / (1 + t ^ 2) at hx
  have ht : (2 : k) / (1 + t ^ 2) ≠ 0 := div_ne_zero (by norm_num) (one_add_sq_ne_zero h t)
  exact ht (by simpa using hx.symm)

theorem quadraticNormCoordinate_chart [CharZero k]
    (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k) :
    quadraticNormCoordinate (quadraticNormChart h t) = t := by
  rw [quadraticNormCoordinate, quadraticNormChart_re_add_one]
  dsimp [quadraticNormChart]
  field_simp [one_add_sq_ne_zero h t]

theorem quadraticNormOne_re_ne_neg_one [CharZero k] (p : QuadraticNormOne k)
    (hp : p ≠ QuadraticNormOne.minusOne) : 1 + p.val.1 ≠ 0 := by
  intro he
  have hx : p.val.1 = -1 := by linear_combination he
  have hn : p.val.1 ^ 2 + p.val.2 ^ 2 = 1 := p.property
  rw [hx] at hn
  have hy : p.val.2 = 0 := by simpa using hn
  apply hp
  apply Subtype.ext
  exact Prod.ext hx hy

theorem quadraticNormChart_coordinate [CharZero k]
    (h : ¬ ∃ r : k, r ^ 2 = -1) (p : QuadraticNormOne k)
    (hp : p ≠ QuadraticNormOne.minusOne) :
    quadraticNormChart h (quadraticNormCoordinate p) = p := by
  have hd := quadraticNormOne_re_ne_neg_one p hp
  have hn : p.val.1 ^ 2 + p.val.2 ^ 2 = 1 := p.property
  have he : 1 + (p.val.2 / (1 + p.val.1)) ^ 2 = 2 / (1 + p.val.1) := by
    field_simp
    linear_combination hn
  apply Subtype.ext
  apply Prod.ext
  · change (1 - (p.val.2 / (1 + p.val.1)) ^ 2) /
      (1 + (p.val.2 / (1 + p.val.1)) ^ 2) = p.val.1
    rw [he]
    field_simp
    linear_combination -hn
  · change (2 * (p.val.2 / (1 + p.val.1))) /
      (1 + (p.val.2 / (1 + p.val.1)) ^ 2) = p.val.2
    rw [he]
    field_simp

theorem quadraticNormChart_continuous
    [TopologicalSpace k] [IsTopologicalDivisionRing k]
    (h : ¬ ∃ r : k, r ^ 2 = -1) : Continuous (quadraticNormChart h) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub (continuous_id.pow 2)).div
    (continuous_const.add (continuous_id.pow 2)) (one_add_sq_ne_zero h)).prodMk
    ((continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) (one_add_sq_ne_zero h))

theorem quadraticNormCoordinate_continuousAt
    [TopologicalSpace k] [IsTopologicalDivisionRing k] [CharZero k]
    (p : QuadraticNormOne k) (hp : p ≠ QuadraticNormOne.minusOne) :
    ContinuousAt quadraticNormCoordinate p := by
  exact (continuous_snd.comp continuous_subtype_val).continuousAt.div
    (continuous_const.add (continuous_fst.comp continuous_subtype_val)).continuousAt
    (quadraticNormOne_re_ne_neg_one p hp)

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormAt.Construction
