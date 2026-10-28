import OAI.Analysis.Calculus.Current.MovingFrame

namespace OAI.Analysis.Calculus.Current

noncomputable section

theorem tangentSlope_antisymmetry {d : ℕ} (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    2 * star (tangentSlope v' z (tangentField v z) b) -
        2 * star (tangentSlope v z (tangentField v' z) b) =
      -(star (tangentField v' z b) - star (tangentField v z b)) / star (z none) := by
  have hs : star (z none) ≠ 0 := star_ne_zero.mpr hY
  cases b with
  | none => simp [tangentSlope, tangentField, tangentVector]
  | some b =>
    cases b with
    | none =>
      simp only [tangentSlope, tangentField, tangentVector,
        ratioSlope_tangentVector z hY, star_div₀, star_neg, star_sum, star_mul,
        star_ofNat, star_sub, Complex.star_def, Complex.conj_ofReal]
      have hh : (∑ i, (v' i : ℂ) * (((v i : ℂ) - star (ratio z i)) /
          (star (z none) * 2))) -
          (∑ i, (v i : ℂ) * (((v' i : ℂ) - star (ratio z i)) /
          (star (z none) * 2))) =
          ((∑ i, (v i : ℂ) * star (ratio z i)) -
            (∑ i, (v' i : ℂ) * star (ratio z i))) / (star (z none) * 2) := by
        simp only [← Finset.sum_sub_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      simp only [Complex.star_def] at hh
      linear_combination -hh
    | some i =>
      simp only [tangentSlope, tangentField, tangentVector,
        ratioSlope_tangentVector z hY, star_div₀, star_add, star_mul,
        star_ofNat, star_sub, Complex.star_def, Complex.conj_ofReal]
      field_simp
      ring

/-- The final residual in (current-final-cancellation) vanishes. This includes
the nonconstant moving-plane contribution, not merely scalar conservation. -/
theorem current_final_cancellation {d : ℕ} (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    (star (tangentField v' z b) - star (tangentField v z b)) / (‖z none‖ : ℂ) +
      star (movingUnit z) *
        (complexBarDirectional (fun w => star (tangentField v' w b)) z (tangentField v z) -
          complexBarDirectional (fun w => star (tangentField v w b)) z (tangentField v' z)) = 0 := by
  rw [complexBarDirectional_conjugate_tangentField v' z _ hY,
    complexBarDirectional_conjugate_tangentField v z _ hY,
    tangentSlope_antisymmetry v v' z hY]
  have hn : (‖z none‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  have hs : star (z none) ≠ 0 := star_ne_zero.mpr hY
  simp only [movingUnit, star_div₀, Complex.star_def, Complex.conj_ofReal] at *
  field_simp
  ring

end
end OAI.Analysis.Calculus.Current
