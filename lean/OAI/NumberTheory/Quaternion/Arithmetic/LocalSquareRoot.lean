import OAI.NumberTheory.Quaternion.Arithmetic.QuadraticNewton

/-! # Local Square Root -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalSquareRoot

noncomputable section

/-! Quadratic Hensel lifting in a complete ultrametric field, proved
by a contraction on a closed ball. -/

open scoped Classical NNReal
open Set

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem exists_local_square_root (a c : K) (ha : ‖a‖ = 1) (h2 : ‖(2 : K)‖ = 1)
    (herr : ‖a ^ 2 - c‖ < 1) : ∃ x : K, x ^ 2 = c ∧ ‖x - a‖ ≤ ‖a ^ 2 - c‖ := by
  let S : Set K := {x | ‖x - a‖ ≤ ‖a ^ 2 - c‖}
  have hS : IsClosed S := isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const))
    continuous_const
  let : CompleteSpace S := hS.isComplete.completeSpace_coe
  have haS : a ∈ S := by
    change ‖a - a‖ ≤ ‖a ^ 2 - c‖
    simpa only [sub_self, norm_zero] using norm_nonneg (a ^ 2 - c)
  let : Nonempty S := ⟨⟨a, haS⟩⟩
  let T : S → S := fun x => ⟨QuadraticNewton.quadraticNewton a c x.val,
    QuadraticNewton.quadraticNewton_maps_ball a c ha h2 herr x.property⟩
  let r : ℝ≥0 := ⟨‖a ^ 2 - c‖, norm_nonneg _⟩
  have hT : ContractingWith r T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    · exact herr
    · change dist (QuadraticNewton.quadraticNewton a c x.val) (QuadraticNewton.quadraticNewton a c y.val) ≤
        ‖a ^ 2 - c‖ * dist x.val y.val
      rw [dist_eq_norm, dist_eq_norm]
      exact QuadraticNewton.quadraticNewton_norm_difference a c ha h2 x.property y.property
  let x := ContractingWith.fixedPoint T hT
  have hfixed : T x = x := hT.fixedPoint_isFixedPt
  have heq : x.val - (x.val ^ 2 - c) / (2 * a) = x.val := congrArg Subtype.val hfixed
  have ha₀ : a ≠ 0 := by intro h; simp [h] at ha
  have h2₀ : (2 : K) ≠ 0 := by intro h; simp [h] at h2
  have hzero : (x.val ^ 2 - c) / (2 * a) = 0 := sub_eq_self.mp heq
  have hnum : x.val ^ 2 - c = 0 := (div_eq_zero_iff).mp hzero |>.resolve_right (mul_ne_zero h2₀ ha₀)
  exact ⟨x.val, sub_eq_zero.mp hnum, x.property⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalSquareRoot
