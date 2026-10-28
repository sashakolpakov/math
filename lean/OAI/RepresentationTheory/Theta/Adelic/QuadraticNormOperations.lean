import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
import OAI.RepresentationTheory.Weil.Local.SquareBall

/-! # Quadratic Norm Operations -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.QuadraticNormOperations

/-! Group operations, two-torsion, and nonarchimedean size estimates in
the rational coordinates of a general quadratic norm-one group. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart.Compact OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart

variable {k : Type*} [Field k] (d : k)

theorem normOne_mul_re (p q : QuadraticNormSquareQuotient.NormOne d) :
    (p * q).val.val.re = p.val.val.re * q.val.val.re + d * p.val.val.im * q.val.val.im := rfl

theorem normOne_mul_im (p q : QuadraticNormSquareQuotient.NormOne d) :
    (p * q).val.val.im = p.val.val.re * q.val.val.im + p.val.val.im * q.val.val.re := by
  change (p.val.val * q.val.val).im = _
  simp only [QuadraticAlgebra.im_mul, zero_mul, add_zero]

theorem normOne_inv_re (p : QuadraticNormSquareQuotient.NormOne d) : (p⁻¹).val.val.re = p.val.val.re := by
  have h := congrArg (fun z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ => z.val.re)
    (QuadraticNormSquareQuotient.conjugate_normOne d p)
  change p.val.val.re + 0 * p.val.val.im = (p⁻¹).val.val.re at h
  simpa only [zero_mul, add_zero] using h.symm

theorem normOne_inv_im (p : QuadraticNormSquareQuotient.NormOne d) : (p⁻¹).val.val.im = -p.val.val.im :=
  (congrArg (fun z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ => z.val.im)
    (QuadraticNormSquareQuotient.conjugate_normOne d p)).symm

theorem normChart_inv (hns : ¬ IsSquare d) (t : k) :
    (QuadraticNormChart.normChart d hns t)⁻¹ = QuadraticNormChart.normChart d hns (-t) := by
  apply QuadraticNormChart.normOne_ext
  · rw [normOne_inv_re]
    change (1 + d * t ^ 2) / (1 - d * t ^ 2) = (1 + d * (-t) ^ 2) / (1 - d * (-t) ^ 2)
    rw [neg_sq]
  · change -(2 * t / (1 - d * t ^ 2)) = 2 * (-t) / (1 - d * (-t) ^ 2)
    simp only [neg_sq, mul_neg, neg_div]

theorem normChart_mul (hns : ¬ IsSquare d) (t u : k) (htu : 1 + d * t * u ≠ 0) :
    QuadraticNormChart.normChart d hns t * QuadraticNormChart.normChart d hns u = QuadraticNormChart.normChart d hns ((t + u) / (1 + d * t * u)) := by
  have hd : 1 - d * ((t + u) / (1 + d * t * u)) ^ 2 =
      (1 - d * t ^ 2) * (1 - d * u ^ 2) / (1 + d * t * u) ^ 2 := by
    field_simp
    ring
  apply QuadraticNormChart.normOne_ext
  · change (1 + d * t ^ 2) / (1 - d * t ^ 2) * ((1 + d * u ^ 2) / (1 - d * u ^ 2)) +
        d * (2 * t / (1 - d * t ^ 2)) * (2 * u / (1 - d * u ^ 2)) =
      (1 + d * ((t + u) / (1 + d * t * u)) ^ 2) / (1 - d * ((t + u) / (1 + d * t * u)) ^ 2)
    rw [hd]
    field_simp [QuadraticNormChart.one_sub_mul_sq_ne_zero d hns t, QuadraticNormChart.one_sub_mul_sq_ne_zero d hns u]
    ring
  · rw [normOne_mul_im]
    change (1 + d * t ^ 2) / (1 - d * t ^ 2) * (2 * u / (1 - d * u ^ 2)) +
        (2 * t / (1 - d * t ^ 2)) * ((1 + d * u ^ 2) / (1 - d * u ^ 2)) =
      (2 * ((t + u) / (1 + d * t * u))) / (1 - d * ((t + u) / (1 + d * t * u)) ^ 2)
    rw [hd]
    field_simp [QuadraticNormChart.one_sub_mul_sq_ne_zero d hns t, QuadraticNormChart.one_sub_mul_sq_ne_zero d hns u]
    ring

def normSquareCoordinate (t : k) : k := 2 * t / (1 + d * t ^ 2)

theorem normChart_sq (hns : ¬ IsSquare d) (t : k) (ht : 1 + d * t ^ 2 ≠ 0) :
    QuadraticNormChart.normChart d hns t ^ 2 = QuadraticNormChart.normChart d hns (normSquareCoordinate d t) := by
  rw [pow_two, normChart_mul d hns t t (by simpa only [pow_two, mul_assoc] using ht)]
  congr 1
  simp only [normSquareCoordinate, pow_two, two_mul, mul_assoc]

theorem normOne_sq_eq_one_iff [CharZero k] (p : QuadraticNormSquareQuotient.NormOne d) :
    p ^ 2 = 1 ↔ p = 1 ∨ p = QuadraticNormChart.minusOne d := by
  constructor
  · intro hp
    rw [pow_two] at hp
    have hx := congrArg (fun q : QuadraticNormSquareQuotient.NormOne d => q.val.val.re) hp
    have hy := congrArg (fun q : QuadraticNormSquareQuotient.NormOne d => q.val.val.im) hp
    rw [normOne_mul_im] at hy
    change p.val.val.re * p.val.val.re + d * p.val.val.im * p.val.val.im = 1 at hx
    change p.val.val.re * p.val.val.im + p.val.val.im * p.val.val.re = 0 at hy
    have hxy : p.val.val.re * p.val.val.im = 0 := by linear_combination (1 / 2 : k) * hy
    have hy0 : p.val.val.im = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · exfalso
        have hn := QuadraticNormChart.normOne_identity d p
        rw [hx0] at hx hn
        have he : (2 : k) = 0 := by linear_combination -hx - hn
        exact (by norm_num : (2 : k) ≠ 0) he
      · exact hy0
    have hx2 : p.val.val.re ^ 2 = 1 := by
      simpa only [hy0, zero_pow two_ne_zero, mul_zero, sub_zero] using QuadraticNormChart.normOne_identity d p
    rcases _root_.sq_eq_one_iff.mp hx2 with hx1 | hx1
    · exact Or.inl (QuadraticNormChart.normOne_ext d hx1 hy0)
    · exact Or.inr (QuadraticNormChart.normOne_ext d hx1 hy0)
  · rintro (rfl | rfl)
    · exact one_pow 2
    · apply QuadraticNormChart.normOne_ext
      · rw [pow_two, normOne_mul_re]
        change (-1 : k) * (-1) + d * 0 * 0 = 1
        ring
      · rw [pow_two, normOne_mul_im]
        change (-1 : k) * 0 + 0 * (-1) = 0
        ring

theorem one_add_mul_norm_eq_one
    {k : Type*} [NormedField k] [IsUltrametricDist k] (d t u : k)
    (r : ℝ) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1) (ht : ‖t‖ < r) (hu : ‖u‖ < r) :
    ‖1 + d * t * u‖ = 1 := by
  have hp : ‖d * t * u‖ < ‖(1 : k)‖ := by
    rw [norm_mul, norm_mul, norm_one]
    calc
      ‖d‖ * ‖t‖ * ‖u‖ ≤ (‖d‖ * r) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.le (norm_nonneg d)) (norm_nonneg u)
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hdr (norm_nonneg u)
      _ < 1 := by simpa only [one_mul] using hu.trans_le hr1
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hp.ne', max_eq_left hp.le, norm_one]

theorem norm_product_coordinate_le
    {k : Type*} [NormedField k] [IsUltrametricDist k] (d t u : k)
    (r : ℝ) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1) (ht : ‖t‖ < r) (hu : ‖u‖ < r) :
    ‖(t + u) / (1 + d * t * u)‖ ≤ max ‖t‖ ‖u‖ := by
  rw [norm_div, one_add_mul_norm_eq_one d t u r hr1 hdr ht hu, div_one]
  exact IsUltrametricDist.norm_add_le_max t u

end RepresentationTheory.Theta.Adelic.QuadraticNormOperations

namespace RepresentationTheory.Theta.Adelic.QuadraticNormOperations.Small

/-! Small open subgroups of a general quadratic norm-one group. Their
coordinate radius explicitly controls the quadratic coefficient. -/

open scoped _root_.Topology

open Set _root_.Metric Filter
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart.Compact
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations

variable {k : Type*} [NormedField k] [IsUltrametricDist k]

def normSmallSubgroup (d : k) (hns : ¬ IsSquare d)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1) : Subgroup (QuadraticNormSquareQuotient.NormOne d) where
  carrier := {p | ∃ t : k, ‖t‖ < r ∧ QuadraticNormChart.normChart d hns t = p}
  one_mem' := ⟨0, by simpa using hr, QuadraticNormChart.normChart_zero d hns⟩
  mul_mem' := by
    rintro p q ⟨t, ht, rfl⟩ ⟨u, hu, rfl⟩
    have hn := one_add_mul_norm_eq_one d t u r hr1 hdr ht hu
    have hd : 1 + d * t * u ≠ 0 := by intro he; simp [he] at hn
    refine ⟨(t + u) / (1 + d * t * u), ?_, (normChart_mul d hns t u hd).symm⟩
    exact (norm_product_coordinate_le d t u r hr1 hdr ht hu).trans_lt (max_lt ht hu)
  inv_mem' := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨-t, by simpa only [norm_neg] using ht, (normChart_inv d hns t).symm⟩

theorem mem_normSmallSubgroup_iff [CharZero k]
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1)
    (p : QuadraticNormSquareQuotient.NormOne d) : p ∈ normSmallSubgroup d hns r hr hr1 hdr ↔
      p ≠ QuadraticNormChart.minusOne d ∧ ‖QuadraticNormChart.normCoordinate d p‖ < r := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨QuadraticNormChart.normChart_ne_minusOne d hns t, by simpa only [QuadraticNormChart.normCoordinate_chart] using ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨QuadraticNormChart.normCoordinate d p, ht, QuadraticNormChart.normChart_coordinate d hns p hp⟩

theorem normSmallSubgroup_isOpen [CharZero k]
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1) :
    IsOpen (normSmallSubgroup d hns r hr hr1 hdr : Set (QuadraticNormSquareQuotient.NormOne d)) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨hpne, hpn⟩ := (mem_normSmallSubgroup_iff d hns r hr hr1 hdr p).mp hp
  have hne : {q : QuadraticNormSquareQuotient.NormOne d | q ≠ QuadraticNormChart.minusOne d} ∈ 𝓝 p := isOpen_ne.mem_nhds hpne
  have hnorm : {q : QuadraticNormSquareQuotient.NormOne d | ‖QuadraticNormChart.normCoordinate d q‖ < r} ∈ 𝓝 p :=
    (QuadraticNormChart.normCoordinate_continuousAt d hns p hpne).norm.preimage_mem_nhds (isOpen_Iio.mem_nhds hpn)
  exact Filter.mem_of_superset (Filter.inter_mem hne hnorm) fun q hq =>
    (mem_normSmallSubgroup_iff d hns r hr hr1 hdr q).mpr hq

theorem normSmallSubgroup_no_two_torsion [CharZero k]
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1)
    (p : QuadraticNormSquareQuotient.NormOne d) (hp : p ∈ normSmallSubgroup d hns r hr hr1 hdr) (hp2 : p ^ 2 = 1) : p = 1 := by
  rcases (normOne_sq_eq_one_iff d p).mp hp2 with hp1 | hpm
  · exact hp1
  · exact ((mem_normSmallSubgroup_iff d hns r hr hr1 hdr p).mp hp).1 hpm |>.elim

def normSmallChart [CharZero k]
    (d : k) (hns : ¬ IsSquare d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1) :
    Metric.ball (0 : k) r ≃ normSmallSubgroup d hns r hr hr1 hdr where
  toFun t := ⟨QuadraticNormChart.normChart d hns t.val, t.val,
    by simpa only [Metric.mem_ball, dist_zero_right] using t.property, rfl⟩
  invFun p := ⟨QuadraticNormChart.normCoordinate d p.val, by
    simpa only [Metric.mem_ball, dist_zero_right] using
      ((mem_normSmallSubgroup_iff d hns r hr hr1 hdr p.val).mp p.property).2⟩
  left_inv t := by apply Subtype.ext; exact QuadraticNormChart.normCoordinate_chart d hns t.val
  right_inv p := by
    apply Subtype.ext
    exact QuadraticNormChart.normChart_coordinate d hns p.val
      ((mem_normSmallSubgroup_iff d hns r hr hr1 hdr p.val).mp p.property).1

omit [IsUltrametricDist k] in
theorem normOne_square_kernel_card [CharZero k] (d : k) :
    Nat.card (powMonoidHom 2 : QuadraticNormSquareQuotient.NormOne d →* QuadraticNormSquareQuotient.NormOne d).ker = 2 := by
  apply Weil.Local.SquareIndexTools.Construction.square_kernel_card_two (QuadraticNormChart.minusOne d)
  · intro he
    have hh : (-1 : k) = 1 := congrArg (fun p : QuadraticNormSquareQuotient.NormOne d => p.val.val.re) he
    norm_num at hh
  · exact normOne_sq_eq_one_iff d

end RepresentationTheory.Theta.Adelic.QuadraticNormOperations.Small

end

end OAI
