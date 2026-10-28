import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra

/-! # Fourier Uniform Bound -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUniformBound.Construction

noncomputable section

/-! A uniform translation radius gives a uniform bound on Fourier support. -/

open _root_.MeasureTheory

theorem fourier_support_bound_of_translation
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (ψ : AddChar F ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (a : F) (ha : ψ a ≠ 1) (ε : ℝ) (hε : 0 < ε)
    (f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ) (ht : ∀ x t, ‖t‖ < ε → f (x + t) = f x)
    (x : Local.FunctionsMetaplectic.Construction.Position F d) (hx : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x ≠ 0) : ‖x‖ ≤ ‖a‖ / ε := by
  have hR : 0 ≤ ‖a‖ / ε := div_nonneg (norm_nonneg _) hε.le
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (hR.trans_lt hi)
  let t : Local.FunctionsMetaplectic.Construction.Position F d := Pi.single i (a / x i)
  have htn : ‖t‖ < ε := by
    rw [show ‖t‖ = ‖a / x i‖ from Pi.norm_single _, norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hxi)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hi
  have hdot : Local.FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [Local.FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  exact hx (FourierUltra.Construction.fourierIntegral_vanishes_of_translation ψ μ f t x
    (fun y => ht y t htn) (by rwa [hdot]))

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUniformBound.Construction
