import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt
import OAI.RepresentationTheory.Weil.Local.SquareBall

/-! # Norm Chart Operations -/

namespace OAI.RepresentationTheory.Weil.Local.NormChartOperations.Construction

noncomputable section

/-! Multiplication, inversion, and squaring in the local rational norm-one coordinates. -/

variable {k : Type*} [Field k]

theorem quadraticNormChart_inv (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k) :
    (QuadraticNormAt.Construction.quadraticNormChart h t)⁻¹ = QuadraticNormAt.Construction.quadraticNormChart h (-t) := by
  apply Subtype.ext
  apply Prod.ext <;> simp [QuadraticNormAt.Construction.quadraticNormChart, QuadraticNormAt.Construction.QuadraticNormOne.inv_val, neg_div]

theorem quadraticNormChart_mul (h : ¬ ∃ r : k, r ^ 2 = -1) (t u : k)
    (htu : 1 - t * u ≠ 0) :
    QuadraticNormAt.Construction.quadraticNormChart h t * QuadraticNormAt.Construction.quadraticNormChart h u =
      QuadraticNormAt.Construction.quadraticNormChart h ((t + u) / (1 - t * u)) := by
  have hd : 1 + ((t + u) / (1 - t * u)) ^ 2 =
      (1 + t ^ 2) * (1 + u ^ 2) / (1 - t * u) ^ 2 := by
    field_simp
    ring
  apply Subtype.ext
  apply Prod.ext
  · change (1 - t ^ 2) / (1 + t ^ 2) * ((1 - u ^ 2) / (1 + u ^ 2)) -
        (2 * t / (1 + t ^ 2)) * (2 * u / (1 + u ^ 2)) =
      (1 - ((t + u) / (1 - t * u)) ^ 2) / (1 + ((t + u) / (1 - t * u)) ^ 2)
    rw [hd]
    field_simp [QuadraticNormAt.Construction.one_add_sq_ne_zero h t, QuadraticNormAt.Construction.one_add_sq_ne_zero h u]
    ring
  · change (1 - t ^ 2) / (1 + t ^ 2) * (2 * u / (1 + u ^ 2)) +
        (2 * t / (1 + t ^ 2)) * ((1 - u ^ 2) / (1 + u ^ 2)) =
      (2 * ((t + u) / (1 - t * u))) / (1 + ((t + u) / (1 - t * u)) ^ 2)
    rw [hd]
    field_simp [QuadraticNormAt.Construction.one_add_sq_ne_zero h t, QuadraticNormAt.Construction.one_add_sq_ne_zero h u]
    ring

theorem quadraticNormChart_sq (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k)
    (ht : 1 - t ^ 2 ≠ 0) :
    QuadraticNormAt.Construction.quadraticNormChart h t ^ 2 = QuadraticNormAt.Construction.quadraticNormChart h (SquareBall.Construction.normOneSquareCoordinate t) := by
  rw [pow_two, quadraticNormChart_mul h t t (by simpa only [pow_two] using ht)]
  congr 1
  dsimp [SquareBall.Construction.normOneSquareCoordinate]
  ring

theorem one_sub_mul_norm_eq_one
    {k : Type*} [NormedField k] [IsUltrametricDist k] (t u : k)
    (ht : ‖t‖ < 1) (hu : ‖u‖ < 1) : ‖1 - t * u‖ = 1 := by
  have hp : ‖-(t * u)‖ < ‖(1 : k)‖ := by
    rw [norm_neg, norm_mul, norm_one]
    exact (mul_le_of_le_one_right (norm_nonneg t) hu.le).trans_lt ht
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hp.ne',
    max_eq_left hp.le, norm_one]

theorem norm_normChart_product_coordinate_le
    {k : Type*} [NormedField k] [IsUltrametricDist k] (t u : k)
    (ht : ‖t‖ < 1) (hu : ‖u‖ < 1) :
    ‖(t + u) / (1 - t * u)‖ ≤ max ‖t‖ ‖u‖ := by
  rw [norm_div, one_sub_mul_norm_eq_one t u ht hu, div_one]
  exact IsUltrametricDist.norm_add_le_max t u

end

end OAI.RepresentationTheory.Weil.Local.NormChartOperations.Construction
