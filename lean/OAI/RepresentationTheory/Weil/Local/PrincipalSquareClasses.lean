import OAI.RepresentationTheory.Weil.Local.SquareBall
import OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup
import Mathlib.Analysis.Normed.Field.UnitBall

/-! # Principal Square Classes -/

namespace OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses.Construction

noncomputable section

section

/-! Compact norm-one units and their principal-unit neighborhoods. -/

open Set _root_.Metric

variable {k : Type*} [NormedField k]

def normUnitSubgroup (k : Type*) [NormedField k] : Subgroup kˣ where
  carrier := {u | ‖u.val‖ = 1}
  one_mem' := norm_one
  mul_mem' := by intro a b ha hb; change ‖a.val * b.val‖ = 1; rw [norm_mul, ha, hb, mul_one]
  inv_mem' := by intro a ha; change ‖(a⁻¹).val‖ = 1; rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

theorem normUnitSubgroup_isCompact [ProperSpace k] :
    IsCompact (normUnitSubgroup k : Set kˣ) := by
  apply Units.isEmbedding_val₀.isCompact_iff.mpr
  have himage : Units.val '' (normUnitSubgroup k : Set kˣ) = Metric.sphere (0 : k) 1 := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change ‖u.val‖ = 1 at hu
      simpa only [Metric.mem_sphere, dist_zero_right] using hu
    · intro hx
      have hx1 : ‖x‖ = 1 := by simpa using hx
      have hx0 : x ≠ 0 := by intro h; simp [h] at hx1
      exact ⟨Units.mk0 x hx0, hx1, rfl⟩
  rw [himage]
  exact isCompact_sphere 0 1

theorem norm_eq_one_of_sub_one_small [IsUltrametricDist k] (x : k) (hx : ‖x - 1‖ < 1) :
    ‖x‖ = 1 := by
  have hh : ‖x - 1‖ < ‖(1 : k)‖ := by simpa using hx
  have hn := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hh.ne
  rw [sub_add_cancel, max_eq_right hh.le, norm_one] at hn
  exact hn

def principalUnitSubgroup [IsUltrametricDist k] (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Subgroup kˣ where
  carrier := {u | ‖u.val - 1‖ < r}
  one_mem' := by simpa using hr
  mul_mem' := by
    intro a b ha hb
    have ha1 := norm_eq_one_of_sub_one_small a.val (ha.trans_le hr1)
    change ‖a.val * b.val - 1‖ < r
    rw [show a.val * b.val - 1 = a.val * (b.val - 1) + (a.val - 1) by ring]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    rw [norm_mul, ha1, one_mul]
    exact max_lt hb ha
  inv_mem' := by
    intro a ha
    have ha1 := norm_eq_one_of_sub_one_small a.val (ha.trans_le hr1)
    change ‖(a⁻¹).val - 1‖ < r
    rw [Units.val_inv_eq_inv_val, show a.val⁻¹ - 1 = -(a.val - 1) / a.val by field_simp; ring,
      norm_div, norm_neg, ha1, div_one]
    exact ha

theorem principalUnitSubgroup_le_normUnitSubgroup [IsUltrametricDist k]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    principalUnitSubgroup r hr hr1 ≤ normUnitSubgroup k :=
  fun a ha => norm_eq_one_of_sub_one_small a.val (ha.trans_le hr1)

theorem principalUnitSubgroup_isOpen [IsUltrametricDist k]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    IsOpen (principalUnitSubgroup (k := k) r hr hr1 : Set kˣ) :=
  isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const

theorem principalUnitSubgroup_no_two_torsion [IsUltrametricDist k] [CharZero k]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hr2 : r ≤ ‖(2 : k)‖)
    (a : kˣ) (ha : a ∈ principalUnitSubgroup r hr hr1) (ha2 : a ^ 2 = 1) : a = 1 := by
  have hs : a.val ^ 2 = 1 := congrArg Units.val ha2
  rcases sq_eq_one_iff.mp hs with h | h
  · exact Units.ext h
  · change ‖a.val - 1‖ < r at ha
    have hh : ‖(-1 : k) - 1‖ < r := by simpa only [h] using ha
    have he : (-1 : k) - 1 = -2 := by ring
    rw [he, norm_neg] at hh
    exact (not_lt_of_ge hr2 hh).elim

def principalUnitChart [IsUltrametricDist k]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Metric.ball (0 : k) r ≃ principalUnitSubgroup (k := k) r hr hr1 where
  toFun x := ⟨Units.mk0 (1 + x.val) (by
    have hxr : ‖x.val‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using x.property
    have hx : ‖x.val‖ < 1 := hxr.trans_le hr1
    intro he
    have hh : ‖(1 + x.val) - 1‖ < 1 := by simpa using hx
    rw [he] at hh
    simp at hh), by
      change ‖(1 + x.val) - 1‖ < r
      simpa only [add_sub_cancel_left, Metric.mem_ball, dist_zero_right] using x.property⟩
  invFun a := ⟨a.val.val - 1, by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖a.val.val - 1‖ < r from a.property)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; apply Units.ext; simp

end

/-! Squares and square cosets in a principal-unit neighborhood. -/

open Set _root_.Metric

variable {k : Type*} [NormedField k] [IsUltrametricDist k]

theorem principalUnit_mem_squares_iff
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (himage : (SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r =
      Metric.ball 0 (‖(2 : k)‖ * r))
    (a : principalUnitSubgroup (k := k) r hr hr1) :
    a ∈ QuadraticNormSubgroup.Construction.squareUnitsSubgroup (principalUnitSubgroup (k := k) r hr hr1) ↔
      ‖a.val.val - 1‖ < ‖(2 : k)‖ * r := by
  constructor
  · rintro ⟨b, hb⟩
    have ht : b.val.val - 1 ∈ Metric.ball (0 : k) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        (show ‖b.val.val - 1‖ < r from b.property)
    have he : SquareBall.Construction.principalSquareCoordinate (b.val.val - 1) = a.val.val - 1 := by
      have hh : b.val.val ^ 2 = a.val.val := congrArg (fun u => u.val.val) hb
      dsimp [SquareBall.Construction.principalSquareCoordinate]
      linear_combination hh
    have hm : a.val.val - 1 ∈ (SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r := ⟨_, ht, he⟩
    rw [himage] at hm
    simpa only [Metric.mem_ball, dist_zero_right] using hm
  · intro ha
    have hm : a.val.val - 1 ∈ (SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r := by
      rw [himage]
      simpa only [Metric.mem_ball, dist_zero_right] using ha
    obtain ⟨t, ht, he⟩ := hm
    refine ⟨principalUnitChart r hr hr1 ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change (1 + t) ^ 2 = a.val.val
    dsimp [SquareBall.Construction.principalSquareCoordinate] at he
    linear_combination he

theorem principalUnit_inverse_mul_norm
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (a b : principalUnitSubgroup (k := k) r hr hr1) :
    ‖(a⁻¹ * b).val.val - 1‖ = ‖(b.val.val - 1) - (a.val.val - 1)‖ := by
  have ha : ‖a.val.val‖ = 1 :=
    principalUnitSubgroup_le_normUnitSubgroup r hr hr1 a.property
  change ‖(a.val⁻¹).val * b.val.val - 1‖ = _
  rw [Units.val_inv_eq_inv_val]
  have he : a.val.val⁻¹ * b.val.val - 1 = (b.val.val - a.val.val) / a.val.val := by field_simp
  rw [he, norm_div, ha, div_one]
  congr 1
  ring

end

end OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses.Construction
