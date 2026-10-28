import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds

/-! # Difference Product -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction

noncomputable section

section

/-! Spatial difference quotients of vector-valued L2 fields, viewed over
the real scalars of the metric energy. -/

open _root_.MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def realL2Translation (m : E) : Lp F 2 (volume : Measure E) →ₗᵢ[ℝ] Lp F 2 (volume : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : E => x + m) (measurePreserving_add_right volume m)

theorem realL2Translation_coe (m : E) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), realL2Translation m u x = u (x + m) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume m)

theorem realL2Translation_zero (u : Lp F 2 (volume : Measure E)) : realL2Translation (0 : E) u = u := by
  apply Lp.ext
  filter_upwards [realL2Translation_coe (0 : E) u] with x hx
  simpa only [add_zero] using hx

theorem realL2Translation_add (m n : E) (u : Lp F 2 (volume : Measure E)) :
    realL2Translation m (realL2Translation n u) = realL2Translation (m + n) u := by
  apply Lp.ext
  filter_upwards [realL2Translation_coe m (realL2Translation n u),
    (measurePreserving_add_right volume m).quasiMeasurePreserving.ae (realL2Translation_coe n u),
    realL2Translation_coe (m + n) u] with x hm hn hmn
  rw [hm, hn, hmn, add_assoc]

theorem realL2Translation_inner (m : E) (u v : Lp F 2 (volume : Measure E)) :
    inner ℝ (realL2Translation m u) v = inner ℝ u (realL2Translation (-m) v) := by
  have h := (realL2Translation m).inner_map_map u (realL2Translation (-m) v)
  rw [realL2Translation_add, add_neg_cancel, realL2Translation_zero] at h
  exact h

def realL2Difference (m : E) (t : ℝ) : Lp F 2 (volume : Measure E) →L[ℝ] Lp F 2 (volume : Measure E) :=
  t⁻¹ • ((realL2Translation (t • m)).toContinuousLinearMap - ContinuousLinearMap.id ℝ _)

theorem realL2Difference_coe (m : E) (t : ℝ) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), realL2Difference m t u x = t⁻¹ • (u (x + t • m) - u x) := by
  filter_upwards [Lp.coeFn_smul t⁻¹ (realL2Translation (t • m) u - u),
    Lp.coeFn_sub (realL2Translation (t • m) u) u, realL2Translation_coe (t • m) u] with x hs hd ht
  change (t⁻¹ • (realL2Translation (t • m) u - u) : Lp F 2 volume) x = _
  simp only [hs, hd, Pi.smul_apply, Pi.sub_apply, ht]

theorem realL2Difference_inner (m : E) (t : ℝ) (u v : Lp F 2 (volume : Measure E)) :
    inner ℝ (realL2Difference m t u) v = -inner ℝ u (realL2Difference m (-t) v) := by
  change inner ℝ (t⁻¹ • (realL2Translation (t • m) u - u)) v =
    -inner ℝ u ((-t)⁻¹ • (realL2Translation ((-t) • m) v - v))
  rw [real_inner_smul_left, inner_sub_left, realL2Translation_inner, real_inner_smul_right, inner_sub_right]
  simp only [inv_neg, neg_smul]
  ring

theorem realL2Difference_eq_complex (m : E) (t : ℝ) (u : Lp ℂ 2 (volume : Measure E)) :
    realL2Difference m t u = DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u := by
  apply Lp.ext
  filter_upwards [realL2Difference_coe m t u, DifferenceQuotients.CM.Construction.l2DifferenceQuotient_coe m t u] with x hr hc
  rw [hr, hc, Complex.real_smul, Complex.ofReal_inv]

end

/-! The exact discrete product rule for measurable operator coefficients,
and uniform coefficient-difference estimates from a Lipschitz bound. -/

open _root_.MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def translatedCoefficient (A : E → F →L[ℝ] F) (m : E) : E → F →L[ℝ] F := fun x => A (x + m)

theorem translatedCoefficient_measurable (A : E → F →L[ℝ] F)
    (hA : AEStronglyMeasurable A (volume : Measure E)) (m : E) :
    AEStronglyMeasurable (translatedCoefficient A m) (volume : Measure E) :=
  hA.comp_measurePreserving (measurePreserving_add_right volume m)

theorem translatedCoefficient_bound (A : E → F →L[ℝ] F)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C) (m : E) :
    ∀ᵐ x ∂(volume : Measure E), ‖translatedCoefficient A m x‖ ≤ C :=
  (measurePreserving_add_right volume m).quasiMeasurePreserving.ae hC

def differenceCoefficient (A : E → F →L[ℝ] F) (m : E) (t : ℝ) : E → F →L[ℝ] F :=
  fun x => t⁻¹ • (A (x + t • m) - A x)

theorem differenceCoefficient_measurable (A : E → F →L[ℝ] F)
    (hA : AEStronglyMeasurable A (volume : Measure E)) (m : E) (t : ℝ) :
    AEStronglyMeasurable (differenceCoefficient A m t) (volume : Measure E) :=
  ((translatedCoefficient_measurable A hA (t • m)).sub hA).const_smul t⁻¹

theorem differenceCoefficient_bound (A : E → F →L[ℝ] F)
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C) (m : E) (t : ℝ) :
    ∀ᵐ x ∂(volume : Measure E), ‖differenceCoefficient A m t x‖ ≤ |t|⁻¹ * (2 * C) := by
  filter_upwards [translatedCoefficient_bound A hC (t • m), hC] with x hx hy
  change ‖t⁻¹ • (A (x + t • m) - A x)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sub_le _ _).trans (by change ‖A (x + t • m)‖ ≤ C at hx; linarith)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A global Lipschitz coefficient bound controls every spatial difference
coefficient uniformly as the translation size tends to zero. -/
theorem differenceCoefficient_lipschitz_bound (A : E → F →L[ℝ] F) {L : NNReal}
    (hA : LipschitzWith L A) (m x : E) (t : ℝ) :
    ‖differenceCoefficient A m t x‖ ≤ (L : ℝ) * ‖m‖ := by
  by_cases ht : t = 0
  · simp only [differenceCoefficient, ht, inv_zero, zero_smul, norm_zero]
    positivity
  have h := hA.dist_le_mul (x + t • m) x
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
  rw [differenceCoefficient, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |t|⁻¹ * ((L : ℝ) * (|t| * ‖m‖)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = (L : ℝ) * ‖m‖ := by field_simp [abs_ne_zero.mpr ht]

/-- The discrete Leibniz rule on actual L2 equivalence classes. -/
theorem realL2Difference_coefficient_product (A : E → F →L[ℝ] F)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (m : E) (t : ℝ) (u : Lp F 2 (volume : Measure E)) :
    realL2Difference m t (LpCoefficients.CM.Construction.boundedFieldLp A hA hC u) =
      LpCoefficients.CM.Construction.boundedFieldLp (translatedCoefficient A (t • m)) (translatedCoefficient_measurable A hA (t • m))
        (translatedCoefficient_bound A hC (t • m)) (realL2Difference m t u) +
      LpCoefficients.CM.Construction.boundedFieldLp (differenceCoefficient A m t) (differenceCoefficient_measurable A hA m t)
        (differenceCoefficient_bound A hC m t) u := by
  let T := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (translatedCoefficient A (t • m))
    (translatedCoefficient_measurable A hA (t • m)) (translatedCoefficient_bound A hC (t • m))
  let R := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (differenceCoefficient A m t)
    (differenceCoefficient_measurable A hA m t) (differenceCoefficient_bound A hC m t)
  apply Lp.ext
  filter_upwards [realL2Difference_coe m t (LpCoefficients.CM.Construction.boundedFieldLp A hA hC u),
    (measurePreserving_add_right volume (t • m)).quasiMeasurePreserving.ae (LpCoefficients.CM.Construction.boundedFieldLp_coe A hA hC u),
    LpCoefficients.CM.Construction.boundedFieldLp_coe A hA hC u, Lp.coeFn_add (T (realL2Difference m t u)) (R u),
    LpCoefficients.CM.Construction.boundedFieldLp_coe _ (translatedCoefficient_measurable A hA (t • m))
      (translatedCoefficient_bound A hC (t • m)) (realL2Difference m t u),
    LpCoefficients.CM.Construction.boundedFieldLp_coe _ (differenceCoefficient_measurable A hA m t)
      (differenceCoefficient_bound A hC m t) u, realL2Difference_coe m t u]
    with x hd ht h0 hadd hT hR hdu
  change realL2Difference m t (LpCoefficients.CM.Construction.boundedFieldLp A hA hC u) x = (T (realL2Difference m t u) + R u) x
  rw [hd, ht, h0, hadd]
  change _ = T (realL2Difference m t u) x + R u x
  rw [hT, hR, hdu]
  simp only [translatedCoefficient, differenceCoefficient, map_smul, map_sub, smul_apply, sub_apply,
    smul_sub]
  abel

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction
